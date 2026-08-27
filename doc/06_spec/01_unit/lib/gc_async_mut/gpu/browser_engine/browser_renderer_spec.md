# Browser Renderer Specification

> Tests covering BrowserRenderer HTML rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 130 | 130 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Specification

## Scenarios

### BrowserRenderer HTML rendering

#### renders inline background blocks without producing a blank frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders inline background blocks without producing a blank frame
   - Expected: pixels.len() equals `TEST_WIDTH * TEST_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders inline background blocks without producing a blank frame")
val html = "<html><body><div style='width: 120px; height: 60px; background-color: #ff0000'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(pixels.len()).to_equal(TEST_WIDTH * TEST_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### renders style block CSS without hanging

- renders style block CSS without hanging
   - Expected: pixels.len() equals `TEST_WIDTH * TEST_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders style block CSS without hanging")
val html = "<html><head><style>body { margin: 0; } .card { width: 100px; height: 50px; background-color: #0000ff; }</style></head><body><div class='card'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(pixels.len()).to_equal(TEST_WIDTH * TEST_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### renders arbitrary non-fixture CSS through layout and paint instead of fill-only fallback

- renders arbitrary non-fixture CSS through layout and paint instead of fill-only fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders arbitrary non-fixture CSS through layout and paint instead of fill-only fallback")
val html = "<html><body style='margin:0; background-color:#ffffff'><div style='width:12px; height:4px; background-color:#2563eb'></div><div style='width:8px; height:4px; background-color:#16a34a'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
```

</details>

#### renders arbitrary non-fixture CSS text through the fallback pixel path

- renders arbitrary non-fixture CSS text through the fallback pixel path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders arbitrary non-fixture CSS text through the fallback pixel path")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { width: 32px; height: 18px; background-color: #e0f2fe; color: #dc2626; font-size: 16px; }</style></head><body><div class='label'>Hi</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFE0F2FEu32)).to_be_greater_than(0)
expect(_count_non_background(result.pixel_data, 0xFFE0F2FEu32)).to_be_greater_than(0)
```

</details>

#### renders input values and placeholders through the text paint path

- renders input values and placeholders through the text paint path


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders input values and placeholders through the text paint path")
val empty = render_html_to_pixels_with_viewport(
    "<html><body style='margin:0;background:#fff'><input style='width:80px;height:20px;color:#111' value=''></body></html>",
    96, 32
).pixel_data
val value = render_html_to_pixels_with_viewport(
    "<html><body style='margin:0;background:#fff'><input style='width:80px;height:20px;color:#111' value='Simple'></body></html>",
    96, 32
).pixel_data
val placeholder = render_html_to_pixels_with_viewport(
    "<html><body style='margin:0;background:#fff'><input style='width:80px;height:20px;color:#111' placeholder='Search'></body></html>",
    96, 32
).pixel_data

expect(_pixels_equal(empty, value)).to_be(false)
expect(_pixels_equal(empty, placeholder)).to_be(false)
```

</details>

#### masks password input by Unicode scalar count

- masks password input by Unicode scalar count


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("masks password input by Unicode scalar count")
val latin = render_html_to_pixels_with_viewport(
    "<html><body style='margin:0;background:#fff'><input type='password' style='width:80px;height:20px' value='x'></body></html>",
    96, 32
).pixel_data
val unicode = render_html_to_pixels_with_viewport(
    "<html><body style='margin:0;background:#fff'><input type='password' style='width:80px;height:20px' value='é'></body></html>",
    96, 32
).pixel_data

expect(_pixels_equal(latin, unicode)).to_be(true)
```

</details>

#### applies later class rules over earlier ones in fallback pixels

- applies later class rules over earlier ones in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies later class rules over earlier ones in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### applies tag rules in fallback pixels

- applies tag rules in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies tag rules in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### renders CSS linear-gradient background images as vertical pixels

- renders CSS linear-gradient background images as vertical pixels
   - Expected: result.pixel_data[0] equals `0xFFDC2626u32`
   - Expected: result.pixel_data[9 * TEST_WIDTH] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS linear-gradient background images as vertical pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 10px; height: 10px; background-image: linear-gradient(#dc2626, #2563eb); }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(result.pixel_data[0]).to_equal(0xFFDC2626u32)
expect(result.pixel_data[9 * TEST_WIDTH]).to_equal(0xFF2563EBu32)
expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### uses ordered fractional quantization for small no-repeat gradient tiles

- uses ordered fractional quantization for small no-repeat gradient tiles
   - Expected: result.pixel_data[0] equals `0xFFE5E7EBu32`
   - Expected: result.pixel_data[19 * TEST_WIDTH] equals `0xFFCBD5E1u32`
   - Expected: result.pixel_data[8 * TEST_WIDTH] equals `0xFFDADFE7u32`
   - Expected: result.pixel_data[1 + 8 * TEST_WIDTH] equals `0xFFDADFE7u32`
   - Expected: result.pixel_data[2 + 8 * TEST_WIDTH] equals `0xFFDAE0E7u32`
   - Expected: result.pixel_data[3 + 9 * TEST_WIDTH] equals `0xFFD9DFE7u32`
   - Expected: result.pixel_data[4 + 10 * TEST_WIDTH] equals `0xFFD8DEE6u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ordered fractional quantization for small no-repeat gradient tiles")
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

- clips gradient background images to background-size when repeat is disabled
   - Expected: result.pixel_data[0] equals `0xFFDC2626u32`
   - Expected: result.pixel_data[5 * TEST_WIDTH] equals `0xFF2563EBu32`
   - Expected: result.pixel_data[6 * TEST_WIDTH] equals `0xFF16A34Au32`
   - Expected: result.pixel_data[6] equals `0xFF16A34Au32`
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 0, 0, 6, 6, 0xFF16A34Au32) equals `36`
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 6, 6, 6, 6, 0xFF16A34Au32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clips gradient background images to background-size when repeat is disabled")
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

- clips background-color to content-box when background-clip requests it
   - Expected: border_box[3 + 3 * 40] equals `0xFF2563EBu32`
   - Expected: content_box[3 + 3 * 40] equals `WHITE_BG`
   - Expected: content_box[7 + 7 * 40] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clips background-color to content-box when background-clip requests it")
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

- positions background images from content-box when background-origin requests it
   - Expected: padding_origin[2 + 2 * 40] equals `0xFF2563EBu32`
   - Expected: content_origin[2 + 2 * 40] equals `0xFF16A34Au32`
   - Expected: content_origin[6 + 6 * 40] equals `0xFF2563EBu32`
   - Expected: _pixels_equal(padding_origin, content_origin) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("positions background images from content-box when background-origin requests it")
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

- positions no-repeat gradient background images within the background color layer
   - Expected: result.pixel_data[0] equals `0xFF16A34Au32`
   - Expected: result.pixel_data[3 + 4 * TEST_WIDTH] equals `0xFFDC2626u32`
   - Expected: result.pixel_data[3 + 9 * TEST_WIDTH] equals `0xFF2563EBu32`
   - Expected: result.pixel_data[2 + 4 * TEST_WIDTH] equals `0xFF16A34Au32`
   - Expected: result.pixel_data[3 + 10 * TEST_WIDTH] equals `0xFF16A34Au32`
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 3, 4, 6, 6, 0xFF16A34Au32) equals `36`
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 0, 0, 3, 4, 0xFF16A34Au32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("positions no-repeat gradient background images within the background color layer")
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

- renders static CSS translate transforms as shifted painted pixels
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 0, 0, 6, 4, WHITE_BG) equals `0`
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 10, 6, 6, 4, WHITE_BG) equals `24`
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders static CSS translate transforms as shifted painted pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 6px; height: 4px; background-color: #2563eb; transform: translate(10px, 6px); }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 0, 0, 6, 4, WHITE_BG)).to_equal(0)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 10, 6, 6, 4, WHITE_BG)).to_equal(24)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(24)
```

</details>

#### renders absolute bottom offsets as bottom anchored painted pixels

- renders absolute bottom offsets as bottom anchored painted pixels
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 2, 0, 6, 4, WHITE_BG) equals `0`
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 2, 13, 6, 4, WHITE_BG) equals `24`
   - Expected: _count_color(result.pixel_data, 0xFF16A34Au32) equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders absolute bottom offsets as bottom anchored painted pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .shell { position: relative; width: 20px; height: 20px; background-color: #ffffff; } .card { position: absolute; left: 2px; bottom: 3px; width: 6px; height: 4px; background-color: #16a34a; }</style></head><body><div class='shell'><div class='card'></div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 2, 0, 6, 4, WHITE_BG)).to_equal(0)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 2, 13, 6, 4, WHITE_BG)).to_equal(24)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(24)
```

</details>

#### renders side-specific border style none without painting disabled sides

- renders side-specific border style none without painting disabled sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders side-specific border style none without painting disabled sides")
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

- renders CSS outline outside border box without affecting flow layout
   - Expected: _count_region_changed(result.pixel_data, TEST_WIDTH, 0, 14, 6, 4, WHITE_BG) equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS outline outside border box without affecting flow layout")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 8px; height: 6px; background-color: #ffffff; outline-width: 2px; outline-style: solid; outline-color: #7c3aed; } .next { width: 6px; height: 4px; background-color: #16a34a; }</style></head><body><div class='card'></div><div class='next'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 0, 14, 6, 4, WHITE_BG)).to_equal(24)
```

</details>

#### renders CSS outline-offset as an expanded outline gap

- renders CSS outline-offset as an expanded outline gap
   - Expected: result.pixel_data[2 + 2 * TEST_WIDTH] equals `0xFF7C3AEDu32`
   - Expected: result.pixel_data[5 + 5 * TEST_WIDTH] equals `WHITE_BG`
   - Expected: result.pixel_data[6 + 6 * TEST_WIDTH] equals `WHITE_BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS outline-offset as an expanded outline gap")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 6px; width: 8px; height: 6px; background-color: #ffffff; outline-width: 1px; outline-style: solid; outline-color: #7c3aed; outline-offset: 3px; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(result.pixel_data[2 + 2 * TEST_WIDTH]).to_equal(0xFF7C3AEDu32)
expect(result.pixel_data[5 + 5 * TEST_WIDTH]).to_equal(WHITE_BG)
expect(result.pixel_data[6 + 6 * TEST_WIDTH]).to_equal(WHITE_BG)
expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
```

</details>

#### renders box-shadow behind the element background box

- renders box-shadow behind the element background box
   - Expected: _count_color(shadow, 0xFF2563EBu32) equals `_count_color(plain, 0xFF2563EBu32)`
   - Expected: _pixels_equal(plain, shadow) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders box-shadow behind the element background box")
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

- renders border-radius by clipping background corner pixels
   - Expected: rounded[4 + 4 * TEST_WIDTH] equals `WHITE_BG`
   - Expected: rounded[10 + 8 * TEST_WIDTH] equals `0xFF2563EBu32`
   - Expected: _pixels_equal(square, rounded) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders border-radius by clipping background corner pixels")
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

- renders border corner radius longhands independently
   - Expected: corner[4 + 4 * TEST_WIDTH] equals `WHITE_BG`
   - Expected: corner[21 + 4 * TEST_WIDTH] equals `0xFF2563EBu32`
   - Expected: corner[4 + 15 * TEST_WIDTH] equals `0xFF2563EBu32`
   - Expected: _pixels_equal(square, corner) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders border corner radius longhands independently")
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

- does not render CSS outline when outline-style disables paint
   - Expected: _count_color(result.pixel_data, 0xFF7C3AEDu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not render CSS outline when outline-style disables paint")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 8px; height: 6px; background-color: #ffffff; outline: 2px solid #7c3aed; outline-style: none; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_equal(0)
```

</details>

#### renders text-transform uppercase with uppercase glyph pixels

- renders text-transform uppercase with uppercase glyph pixels
   - Expected: _pixels_equal(lower, transformed) is false
   - Expected: _pixels_equal(upper, transformed) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders text-transform uppercase with uppercase glyph pixels")
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

- renders text-decoration underline below text glyphs
   - Expected: _pixels_equal(plain, underline) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders text-decoration underline below text glyphs")
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>UNDERLINE</div></body></html>"
val underline_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; text-decoration: underline; }</style></head><body><div class='label'>UNDERLINE</div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, 96, 32).pixel_data
val underline = render_html_to_pixels_with_viewport(underline_html, 96, 32).pixel_data

expect(_count_color(underline, 0xFF111827u32)).to_be_greater_than(_count_color(plain, 0xFF111827u32))
expect(_pixels_equal(plain, underline)).to_equal(false)
```

</details>

#### renders text-decoration-color independently from text color

- renders text-decoration-color independently from text color


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders text-decoration-color independently from text color")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #2563eb; font-size: 8px; text-decoration-line: underline; text-decoration-color: #dc2626; }</style></head><body><div class='label'>UNDERLINE</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, 96, 32).pixel_data

expect(_count_color(result, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

#### renders text-indent by shifting the first text line right

- renders text-indent by shifting the first text line right
   - Expected: _count_color(indented, 0xFF111827u32) equals `_count_color(plain, 0xFF111827u32)`
   - Expected: _pixels_equal(plain, indented) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders text-indent by shifting the first text line right")
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

- renders letter-spacing by spreading glyph advances
   - Expected: _count_color(spaced, 0xFF111827u32) equals `_count_color(plain, 0xFF111827u32)`
   - Expected: _pixels_equal(plain, spaced) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders letter-spacing by spreading glyph advances")
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

- renders word-spacing by widening space advances
   - Expected: _count_color(spaced, 0xFF111827u32) equals `_count_color(plain, 0xFF111827u32)`
   - Expected: _pixels_equal(plain, spaced) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders word-spacing by widening space advances")
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

- renders font-style italic with skewed glyph pixels
   - Expected: _count_color(italic, 0xFF111827u32) equals `_count_color(plain, 0xFF111827u32)`
   - Expected: _pixels_equal(plain, italic) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders font-style italic with skewed glyph pixels")
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

- renders direction rtl by reversing simple text glyph order
   - Expected: _count_color(rtl, 0xFF111827u32) equals `_count_color(reversed, 0xFF111827u32)`
   - Expected: _pixels_equal(ltr, rtl) is false
   - Expected: _pixels_equal(reversed, rtl) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders direction rtl by reversing simple text glyph order")
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

- renders text-shadow behind foreground text glyphs
   - Expected: _count_color(shadow, 0xFF111827u32) equals `_count_color(plain, 0xFF111827u32)`
   - Expected: _pixels_equal(plain, shadow) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders text-shadow behind foreground text glyphs")
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

- renders text-overflow ellipsis for clipped nowrap text
   - Expected: _pixels_equal(clipped, ellipsis) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders text-overflow ellipsis for clipped nowrap text")
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

- applies class rules over tag rules in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies class rules over tag rules in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### does not match class selector prefixes in fallback pixels

- does not match class selector prefixes in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not match class selector prefixes in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card-title { width: 12px; height: 8px; background-color: #2563eb; } .card { width: 12px; height: 8px; background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### applies exact selectors from comma selector lists in fallback pixels

- applies exact selectors from comma selector lists in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies exact selectors from comma selector lists in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } section, .card { width: 12px; height: 8px; background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
```

</details>

#### ignores specificity from unmatched selector-list branches in fallback pixels

- ignores specificity from unmatched selector-list branches in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores specificity from unmatched selector-list branches in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } #missing, div { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### lets stylesheet important beat a higher-specificity normal rule in fallback pixels

- lets stylesheet important beat a higher-specificity normal rule in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF16A34Au32) equals `96`
   - Expected: _count_color(result.pixel_data, 0xFFEF4444u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets stylesheet important beat a higher-specificity normal rule in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 8px; background-color: #16a34a !important; } #target { background-color: #ef4444; }</style></head><body><div id='target' class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(
    html, TEST_WIDTH, TEST_HEIGHT
)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(96)
expect(_count_color(result.pixel_data, 0xFFEF4444u32)).to_equal(0)
```

</details>

#### lets stylesheet important beat inline normal style in fallback pixels

- lets stylesheet important beat inline normal style in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF16A34Au32) equals `96`
   - Expected: _count_color(result.pixel_data, 0xFFEF4444u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets stylesheet important beat inline normal style in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 8px; background-color: #16a34a ! ImPoRtAnT; }</style></head><body><div class='card' style='background-color:#ef4444'></div></body></html>"
val result = render_html_to_pixels_with_viewport(
    html, TEST_WIDTH, TEST_HEIGHT
)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(96)
expect(_count_color(result.pixel_data, 0xFFEF4444u32)).to_equal(0)
```

</details>

#### orders competing important declarations in fallback pixels

- orders competing important declarations in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `96`
   - Expected: _count_color(result.pixel_data, 0xFF16A34Au32) equals `96`
   - Expected: _count_color(result.pixel_data, 0xFFEF4444u32) equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("orders competing important declarations in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 8px; background-color: #16a34a !important; } #first { background-color: #2563eb !important; } #second { background-color: #2563eb !important; background-color: #16a34a !important; }</style></head><body><div id='first' class='card'></div><div id='second' class='card'></div><div class='card' style='background-color:#ef4444 !important'></div></body></html>"
val result = render_html_to_pixels_with_viewport(
    html, TEST_WIDTH, TEST_HEIGHT
)

expect(result.pixel_data[1 * TEST_WIDTH + 1]).to_equal(
    0xFF2563EBu32
)
expect(result.pixel_data[9 * TEST_WIDTH + 1]).to_equal(
    0xFF16A34Au32
)
expect(result.pixel_data[17 * TEST_WIDTH + 1]).to_equal(
    0xFFEF4444u32
)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(96)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(96)
expect(_count_color(result.pixel_data, 0xFFEF4444u32)).to_equal(96)
```

</details>

#### applies :is selector lists in fallback pixels

- applies :is selector lists in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :is selector lists in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } :is(section, .card) { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### applies :where selector lists in fallback pixels

- applies :where selector lists in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :where selector lists in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } :where(section, .card) { width: 12px; height: 8px; background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
```

</details>

#### applies tag qualified :is selectors in fallback pixels

- applies tag qualified :is selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies tag qualified :is selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:is(.card, .panel) { width: 12px; height: 8px; background-color: #dc2626; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

#### applies :not selector lists in fallback pixels

- applies :not selector lists in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :not selector lists in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_be_greater_than(0)
```

</details>

#### rejects :not selectors when an option matches

- rejects :not selectors when an option matches
   - Expected: _count_color(result.pixel_data, 0xFF0891B2u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :not selectors when an option matches")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.card, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_equal(0)
```

</details>

#### applies :has descendant selectors in fallback pixels

- applies :has descendant selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :has descendant selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
```

</details>

#### applies :has direct child selectors in fallback pixels

- applies :has direct child selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :has direct child selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### rejects :has direct child selectors for nested descendants

- rejects :has direct child selectors for nested descendants
   - Expected: _count_color(result.pixel_data, 0xFF0E7490u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :has direct child selectors for nested descendants")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><section><span class='badge'></span></section></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### rejects :has selectors when no descendant option matches

- rejects :has selectors when no descendant option matches
   - Expected: _count_color(result.pixel_data, 0xFF7C3AEDu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :has selectors when no descendant option matches")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(.badge, strong) { width: 12px; height: 8px; background-color: #7c3aed; }</style></head><body><div><span class='label'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_equal(0)
```

</details>

#### applies :empty selectors in fallback pixels

- applies :empty selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :empty selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### rejects :empty selectors when the fallback div has content

- rejects :empty selectors when the fallback div has content
   - Expected: _count_color(result.pixel_data, 0xFF0F766Eu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :empty selectors when the fallback div has content")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div>content</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_equal(0)
```

</details>

#### applies :first-child selectors in fallback pixels

- applies :first-child selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :first-child selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### rejects :first-child selectors for later fallback divs

- rejects :first-child selectors for later fallback divs
   - Expected: _count_color(result.pixel_data, 0xFF1D4ED8u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :first-child selectors for later fallback divs")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_equal(0)
```

</details>

#### applies :last-child selectors in fallback pixels

- applies :last-child selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :last-child selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### rejects :last-child selectors for earlier fallback divs

- rejects :last-child selectors for earlier fallback divs
   - Expected: _count_color(result.pixel_data, 0xFFBE123Cu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :last-child selectors for earlier fallback divs")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_equal(0)
```

</details>

#### applies :only-child selectors in fallback pixels

- applies :only-child selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :only-child selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_be_greater_than(0)
```

</details>

#### rejects :only-child selectors when a sibling exists

- rejects :only-child selectors when a sibling exists
   - Expected: _count_color(result.pixel_data, 0xFF9333EAu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :only-child selectors when a sibling exists")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_equal(0)
```

</details>

#### applies :nth-child odd and even selectors in fallback pixels

- applies :nth-child odd and even selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :nth-child odd and even selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:nth-child(even) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### rejects :nth-child odd selectors for even fallback nodes

- rejects :nth-child odd selectors for even fallback nodes
   - Expected: _count_color(result.pixel_data, 0xFF0E7490u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :nth-child odd selectors for even fallback nodes")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(odd) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### applies :nth-child an plus b selectors in fallback pixels

- applies :nth-child an plus b selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies :nth-child an plus b selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(2n+1) { width: 12px; height: 8px; background-color: #7c2d12; }</style></head><body><div></div><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C2D12u32)).to_be_greater_than(0)
```

</details>

#### rejects :nth-child an plus b selectors for non matching fallback nodes

- rejects :nth-child an plus b selectors for non matching fallback nodes
   - Expected: _count_color(result.pixel_data, 0xFF7C2D12u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects :nth-child an plus b selectors for non matching fallback nodes")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(2n+1) { width: 12px; height: 8px; background-color: #7c2d12; }</style></head><body><div></div><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C2D12u32)).to_equal(0)
```

</details>

#### applies simple rules nested inside CSS layer blocks

- applies simple rules nested inside CSS layer blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies simple rules nested inside CSS layer blocks")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### applies functional selectors nested inside CSS layer blocks

- applies functional selectors nested inside CSS layer blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies functional selectors nested inside CSS layer blocks")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { div:not(.disabled) { width: 12px; height: 8px; background-color: #be123c; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### normalizes simple CSS nesting before fallback selector scans

- normalizes simple CSS nesting before fallback selector scans
   - Expected: normalized_document_style does not contain `&.primary`
   - Expected: normalized_html does not contain `&.primary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes simple CSS nesting before fallback selector scans")
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

- applies simple CSS nesting with parent selector references


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies simple CSS nesting with parent selector references")
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

- applies simple descendant rules from CSS nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies simple descendant rules from CSS nesting")
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

- applies attribute presence selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute presence selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-card] { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div data-card='true'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### applies exact attribute value selectors in fallback pixels

- applies exact attribute value selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies exact attribute value selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='active'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4D7C0Fu32)).to_be_greater_than(0)
```

</details>

#### applies exact quoted attribute value selectors containing spaces

- applies exact quoted attribute value selectors containing spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies exact quoted attribute value selectors containing spaces")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-label='primary action'] { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div data-label='primary action'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### rejects exact attribute value selectors with different values

- rejects exact attribute value selectors with different values
   - Expected: _count_color(result.pixel_data, 0xFF4D7C0Fu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects exact attribute value selectors with different values")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='inactive'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4D7C0Fu32)).to_equal(0)
```

</details>

#### applies attribute prefix selectors in fallback pixels

- applies attribute prefix selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute prefix selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }</style></head><body><div data-route='/app/home'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F5E9Cu32)).to_be_greater_than(0)
```

</details>

#### applies attribute suffix selectors in fallback pixels

- applies attribute suffix selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute suffix selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF065F46u32)).to_be_greater_than(0)
```

</details>

#### rejects attribute suffix selectors without a matching suffix

- rejects attribute suffix selectors without a matching suffix
   - Expected: _count_color(result.pixel_data, 0xFF065F46u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects attribute suffix selectors without a matching suffix")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings/profile'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF065F46u32)).to_equal(0)
```

</details>

#### applies attribute substring selectors in fallback pixels

- applies attribute substring selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute substring selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-tags*='beta'] { width: 12px; height: 8px; background-color: #9d174d; }</style></head><body><div data-tags='alpha-beta-release'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF9D174Du32)).to_be_greater_than(0)
```

</details>

#### applies attribute whitespace token selectors in fallback pixels

- applies attribute whitespace token selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute whitespace token selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-flags~='selected'] { width: 12px; height: 8px; background-color: #7c2d12; }</style></head><body><div data-flags='primary selected visible'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C2D12u32)).to_be_greater_than(0)
```

</details>

#### applies attribute dash match selectors in fallback pixels

- applies attribute dash match selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies attribute dash match selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }</style></head><body><div lang='en-US'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF155E75u32)).to_be_greater_than(0)
```

</details>

#### rejects attribute dash match selectors without a boundary

- rejects attribute dash match selectors without a boundary
   - Expected: _count_color(result.pixel_data, 0xFF155E75u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects attribute dash match selectors without a boundary")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }</style></head><body><div lang='english'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF155E75u32)).to_equal(0)
```

</details>

#### applies case insensitive attribute selectors in fallback pixels

- applies case insensitive attribute selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies case insensitive attribute selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='dialog' i] { width: 12px; height: 8px; background-color: #4338ca; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4338CAu32)).to_be_greater_than(0)
```

</details>

#### keeps attribute selectors case sensitive without the i flag

- keeps attribute selectors case sensitive without the i flag
   - Expected: _count_color(result.pixel_data, 0xFF4338CAu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps attribute selectors case sensitive without the i flag")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='dialog'] { width: 12px; height: 8px; background-color: #4338ca; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4338CAu32)).to_equal(0)
```

</details>

#### applies explicit case sensitive attribute selectors in fallback pixels

- applies explicit case sensitive attribute selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies explicit case sensitive attribute selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='Dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### rejects explicit case sensitive attribute selectors with different case

- rejects explicit case sensitive attribute selectors with different case
   - Expected: _count_color(result.pixel_data, 0xFF1D4ED8u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects explicit case sensitive attribute selectors with different case")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_equal(0)
```

</details>

#### applies tag class compound selectors in fallback pixels

- applies tag class compound selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies tag class compound selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div.card { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### applies tag class compound selectors over bare class selectors in fallback pixels

- applies tag class compound selectors over bare class selectors in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF16A34Au32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies tag class compound selectors over bare class selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div.card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(0)
```

</details>

#### applies multi class selectors in fallback pixels regardless of class order

- applies multi class selectors in fallback pixels regardless of class order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies multi class selectors in fallback pixels regardless of class order")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='primary card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### applies multi class selectors over bare class selectors in fallback pixels

- applies multi class selectors over bare class selectors in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF16A34Au32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies multi class selectors over bare class selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card primary'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(0)
```

</details>

#### applies id rules over class rules in fallback pixels

- applies id rules over class rules in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies id rules over class rules in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 8px; background-color: #2563eb; } #hero { background-color: #dc2626; }</style></head><body><div id='hero' class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### applies tag id compound selectors in fallback pixels

- applies tag id compound selectors in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies tag id compound selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div#hero { width: 12px; height: 8px; background-color: #dc2626; }</style></head><body><div id='hero'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

#### applies tag id compound selectors over bare id selectors in fallback pixels

- applies tag id compound selectors over bare id selectors in fallback pixels
   - Expected: _count_color(result.pixel_data, 0xFF2563EBu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies tag id compound selectors over bare id selectors in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div#hero { width: 12px; height: 8px; background-color: #dc2626; } #hero { background-color: #2563eb; }</style></head><body><div id='hero'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### renders simple nested span text in fallback pixels

- renders simple nested span text in fallback pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders simple nested span text in fallback pixels")
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #fef3c7; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFFEF3C7u32)).to_be_greater_than(0)
expect(_count_non_background(result.pixel_data, 0xFFFEF3C7u32)).to_be_greater_than(0)
```

</details>

#### uses nested span style when rendering fallback text pixels

- uses nested span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses nested span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span style='color:#dc2626'>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span style='color:#16a34a'>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor descendant span style when rendering fallback text pixels

- uses ancestor descendant span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ancestor descendant span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card span { color:#dc2626; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card span { color:#16a34a; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor id descendant span style when rendering fallback text pixels

- uses ancestor id descendant span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ancestor id descendant span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } #hero { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } #hero span { color:#dc2626; }</style></head><body><div id='hero'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } #hero { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } #hero span { color:#16a34a; }</style></head><body><div id='hero'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor child span style when rendering fallback text pixels

- uses ancestor child span style when rendering fallback text pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ancestor child span style when rendering fallback text pixels")
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card > span { color:#dc2626; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card > span { color:#16a34a; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### paints inline background shorthand fallback colors after url tokens

- paints inline background shorthand fallback colors after url tokens
   - Expected: _scene_has_fill_color(html, 0xFF00FF88u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints inline background shorthand fallback colors after url tokens")
val html = "<html><body><div style='width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### paints style block background shorthand fallback colors after url tokens

- paints style block background shorthand fallback colors after url tokens
   - Expected: _scene_has_fill_color(html, 0xFF00FF88u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints style block background shorthand fallback colors after url tokens")
val html = "<html><head><style>.card { width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### resolves background-color currentColor from the computed text color

- resolves background-color currentColor from the computed text color
   - Expected: _scene_has_fill_color(html, 0xFF123456u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves background-color currentColor from the computed text color")
val html = "<html><body><div style='width: 80px; height: 40px; color: #123456; background-color: currentColor'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF123456u32)).to_equal(true)
```

</details>

#### resolves background shorthand currentColor from the computed text color

- resolves background shorthand currentColor from the computed text color
   - Expected: _scene_has_fill_color(html, 0xFF345678u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves background shorthand currentColor from the computed text color")
val html = "<html><body><div style='width: 80px; height: 40px; color: #345678; background: currentColor no-repeat'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF345678u32)).to_equal(true)
```

</details>

#### resolves inline currentColor backgrounds even when color is declared later

- resolves inline currentColor backgrounds even when color is declared later
   - Expected: _scene_has_fill_color(html, 0xFF456789u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves inline currentColor backgrounds even when color is declared later")
val html = "<html><body><div style='width: 80px; height: 40px; background-color: currentColor; color: #456789'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF456789u32)).to_equal(true)
```

</details>

#### resolves style block currentColor backgrounds from rule color

- resolves style block currentColor backgrounds from rule color
   - Expected: _scene_has_fill_color(html, 0xFF56789Au32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves style block currentColor backgrounds from rule color")
val html = "<html><head><style>.card { width: 80px; height: 40px; background-color: currentColor; color: #56789a; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF56789Au32)).to_equal(true)
```

</details>

#### resolves style block currentColor backgrounds after later matched color rules

- resolves style block currentColor backgrounds after later matched color rules
   - Expected: _scene_has_fill_color(html, 0xFF6789ABu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves style block currentColor backgrounds after later matched color rules")
val html = "<html><head><style>.card { width: 80px; height: 40px; background-color: currentColor; } .card { color: #6789ab; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF6789ABu32)).to_equal(true)
```

</details>

#### resolves CSS custom properties from style blocks

- resolves CSS custom properties from style blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves CSS custom properties from style blocks")
val blue_html = "<html><head><style>:root { --theme-panel: #0000ff; } body { margin: 0; background-color: #ffffff; } .card { width: 100px; height: 50px; background-color: var(--theme-panel); }</style></head><body><div class='card'></div></body></html>"
val green_html = "<html><head><style>:root { --theme-panel: #00ff00; } body { margin: 0; background-color: #ffffff; } .card { width: 100px; height: 50px; background-color: var(--theme-panel); }</style></head><body><div class='card'></div></body></html>"
val blue = render_html_to_pixels_with_viewport(blue_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
assert_not_equal(_pixel_signature(blue), _pixel_signature(green))
```

</details>

#### renders the glass style body fixture

- renders the glass style body fixture
   - Expected: pixels.len() equals `TEST_WIDTH * TEST_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders the glass style body fixture")
val html = "<html><head><style>body { margin: 0; background-color: #101820; color: #f3f4f6; } .panel { width: 120px; height: 70px; background-color: #1f2937; }</style></head><body><div class='panel'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(pixels.len()).to_equal(TEST_WIDTH * TEST_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### is deterministic for repeated renders of the same HTML

- is deterministic for repeated renders of the same HTML
   - Expected: _pixel_signature(first) equals `_pixel_signature(second)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic for repeated renders of the same HTML")
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #22aa44'></div></body></html>"
val first = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val second = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(_pixel_signature(first)).to_equal(_pixel_signature(second))
```

</details>

#### uses the same pixels as an explicit Engine2D software renderer

- uses the same pixels as an explicit Engine2D software renderer
   - Expected: default_renderer.engine == nil is true
   - Expected: software_renderer.engine == nil is false
   - Expected: default_renderer.backend_name() equals `software`
   - Expected: software_renderer.backend_name() equals `software`
   - Expected: _pixels_equal(default_pixels, software_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses the same pixels as an explicit Engine2D software renderer")
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #2050a0'></div><span style='color:#ffffff'>Hi</span></body></html>"
val default_renderer = BrowserRenderer.create(TEST_WIDTH, TEST_HEIGHT)
val software_renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val default_pixels = default_renderer.render_html_to_pixels(html).pixel_data
val software_pixels = software_renderer.render_html_to_pixels(html).pixel_data
expect(default_renderer.engine == nil).to_equal(true)
expect(software_renderer.engine == nil).to_equal(false)
expect(default_renderer.backend_name()).to_equal("software")
expect(software_renderer.backend_name()).to_equal("software")
expect(_pixels_equal(default_pixels, software_pixels)).to_equal(true)
```

</details>

#### reports deterministic software for unknown backend fallback

- reports deterministic software for unknown backend fallback
   - Expected: renderer.engine == nil is true
   - Expected: renderer.backend_name() equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports deterministic software for unknown backend fallback")
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "not-a-backend")
expect(renderer.engine == nil).to_equal(true)
expect(renderer.backend_name()).to_equal("software")
```

</details>

#### module pixel helper matches explicit Engine2D software rendering

- module pixel helper matches explicit Engine2D software rendering
   - Expected: _pixels_equal(helper_pixels, renderer_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("module pixel helper matches explicit Engine2D software rendering")
val html = "<html><body><div style='width: 110px; height: 30px; background-color: #aa2244'></div></body></html>"
val helper_pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val renderer_pixels = renderer.render_html_to_pixels(html).pixel_data
expect(_pixels_equal(helper_pixels, renderer_pixels)).to_equal(true)
```

</details>

#### renders famous-site corpus block at Chrome default body margin

- renders famous-site corpus block at Chrome default body margin
   - Expected: pixels.len() equals `160 * 120`
   - Expected: pixels[0] equals `0xFFFFFFFFu32`
   - Expected: pixels[7 + 7 * 160] equals `0xFFFFFFFFu32`
   - Expected: pixels[8 + 8 * 160] equals `0xFF2563EBu32`
   - Expected: pixels[127 + 47 * 160] equals `0xFF2563EBu32`
   - Expected: pixels[128 + 48 * 160] equals `0xFFFFFFFFu32`
   - Expected: _count_region_changed(pixels, 160, 128, 8, 32, 40, 0xFFFFFFFFu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders famous-site corpus block at Chrome default body margin")
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

- Engine2D bridge keeps explicit backend rendering available
   - Expected: bridge_renderer.engine == nil is false
   - Expected: explicit_renderer.engine == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Engine2D bridge keeps explicit backend rendering available")
val html = "<html><body><div style='width: 70px; height: 24px; background-color: #4488cc'></div></body></html>"
val bridge_renderer = create_software_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val explicit_renderer = create_gpu_browser_renderer_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
expect(bridge_renderer.engine == nil).to_equal(false)
expect(explicit_renderer.engine == nil).to_equal(false)
expect(_pixels_equal(
    bridge_renderer.render_html_to_pixels(html).pixel_data,
    explicit_renderer.render_html_to_pixels(html).pixel_data
)).to_equal(true)
```

</details>

#### Engine2D GPU bridge requests Metal while preserving CPU parity fallback

- Engine2D GPU bridge requests Metal while preserving CPU parity fallback
   - Expected: gpu_renderer.backend_name() equals `metal`
   - Expected: cpu_renderer.backend_name() equals `cpu`
   - Expected: _pixels_equal(gpu_pixels, cpu_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Engine2D GPU bridge requests Metal while preserving CPU parity fallback")
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

- renders CSS background fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[0] equals `0xFFF0F0F8u32`
   - Expected: pixels[8 + 8 * 40] equals `0xFFD0D8E8u32`
   - Expected: pixels[27 + 61 * 40] equals `0xFFBFDBFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS background fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[0]).to_equal(0xFFF0F0F8u32)
expect(pixels[8 + 8 * 40]).to_equal(0xFFD0D8E8u32)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS color fixture pixels through BrowserRenderer

- renders CSS color fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[8 + 8 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[8 + 28 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[8 + 48 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS color fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("10_colors"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[8 + 8 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[8 + 28 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[8 + 48 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS padding fixture pixels through BrowserRenderer

- renders CSS padding fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 90`
   - Expected: pixels[16 + 16 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[22 + 50 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[22 + 78 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS padding fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("12_padding"), 40, 90).pixel_data
expect(pixels.len()).to_equal(40 * 90)
expect(pixels[16 + 16 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 50 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 78 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS margin fixture pixels through BrowserRenderer

- renders CSS margin fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 95`
   - Expected: pixels[14 + 14 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[22 + 52 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[22 + 82 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS margin fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("13_margin"), 40, 95).pixel_data
expect(pixels.len()).to_equal(40 * 95)
expect(pixels[14 + 14 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 52 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 82 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### resolves vertical viewport margins against viewport height

- resolves vertical viewport margins against viewport height
   - Expected: pixels[10 + 79 * 200] equals `WHITE_BG`
   - Expected: pixels[10 + 80 * 200] equals `0xFF3050A0u32`
   - Expected: pixels[10 + 99 * 200] equals `0xFF3050A0u32`
   - Expected: pixels[10 + 100 * 200] equals `WHITE_BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves vertical viewport margins against viewport height")
val html = "<html><body style='margin:0'><div style='width:100px;height:20px;margin-top:40vh;background-color:#3050a0'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 200, 200).pixel_data

expect(pixels[10 + 79 * 200]).to_equal(WHITE_BG)
expect(pixels[10 + 80 * 200]).to_equal(0xFF3050A0u32)
expect(pixels[10 + 99 * 200]).to_equal(0xFF3050A0u32)
expect(pixels[10 + 100 * 200]).to_equal(WHITE_BG)
```

</details>

#### renders CSS border fixture pixels through BrowserRenderer

- renders CSS border fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[4 + 4 * 40] equals `0xFF000000u32`
   - Expected: pixels[15 + 18 * 40] equals `0xFF003366u32`
   - Expected: pixels[24 + 61 * 40] equals `0xFF006600u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS border fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("14_border"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[4 + 4 * 40]).to_equal(0xFF000000u32)
expect(pixels[15 + 18 * 40]).to_equal(0xFF003366u32)
expect(pixels[24 + 61 * 40]).to_equal(0xFF006600u32)
```

</details>

#### renders CSS flex row fixture pixels through BrowserRenderer

- renders CSS flex row fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `125 * 70`
   - Expected: pixels[121 + 61 * 125] equals `0xFF93C5FDu32`
   - Expected: pixels[27 + 61 * 125] equals `0xFFBFDBFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS flex row fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("16_flex_row"), 125, 70).pixel_data
expect(pixels.len()).to_equal(125 * 70)
expect(pixels[121 + 61 * 125]).to_equal(0xFF93C5FDu32)
expect(pixels[27 + 61 * 125]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS flex column fixture pixels through BrowserRenderer

- renders CSS flex column fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 100`
   - Expected: pixels[27 + 61 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[27 + 95 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS flex column fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("17_flex_col"), 40, 100).pixel_data
expect(pixels.len()).to_equal(40 * 100)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[27 + 95 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### parses rgb() background-color in the fallback pixel path

- parses rgb() background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses rgb() background-color in the fallback pixel path")
val html = "<html><body style='background-color: rgb(37, 99, 235)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF2563EBu32)
```

</details>

#### parses modern space-separated rgb() background-color in the fallback pixel path

- parses modern space-separated rgb() background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF059669u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses modern space-separated rgb() background-color in the fallback pixel path")
val html = "<html><body style='background-color: rgb(5 150 105)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### composites rgba() background-color over the white page in the fallback pixel path

- composites rgba() background-color over the white page in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF808080u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites rgba() background-color over the white page in the fallback pixel path")
val html = "<html><body style='background-color: rgba(0, 0, 0, 0.5)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF808080u32)
```

</details>

#### parses shorthand hex background-color in the fallback pixel path

- parses shorthand hex background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF00FF88u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses shorthand hex background-color in the fallback pixel path")
val html = "<html><body style='background-color: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### composites shorthand hex alpha background-color over the white page in the fallback pixel path

- composites shorthand hex alpha background-color over the white page in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF777777u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites shorthand hex alpha background-color over the white page in the fallback pixel path")
val html = "<html><body style='background-color: #0008'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF777777u32)
```

</details>

#### parses named CSS background-color in the fallback pixel path

- parses named CSS background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF663399u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses named CSS background-color in the fallback pixel path")
val html = "<html><body style='background-color: rebeccapurple'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### composites transparent background-color to the white page in the fallback pixel path

- composites transparent background-color to the white page in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites transparent background-color to the white page in the fallback pixel path")
val html = "<html><body style='background-color: transparent'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
```

</details>

#### parses hsl() background-color in the fallback pixel path

- parses hsl() background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF008000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses hsl() background-color in the fallback pixel path")
val html = "<html><body style='background-color: hsl(120, 100%, 25%)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF008000u32)
```

</details>

#### parses color-first background shorthand in the fallback pixel path

- parses color-first background shorthand in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF663399u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses color-first background shorthand in the fallback pixel path")
val html = "<html><body style='background: rebeccapurple no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### parses function color background shorthand before trailing tokens

- parses function color background shorthand before trailing tokens
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF059669u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses function color background shorthand before trailing tokens")
val html = "<html><body style='background: rgb(5, 150, 105) no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### parses fallback color after url() in background shorthand

- parses fallback color after url() in background shorthand
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF00FF88u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses fallback color after url() in background shorthand")
val html = "<html><body style='background: url(hero.png) #0f8 no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background shorthand override earlier background-color in fallback pixels

- lets later background shorthand override earlier background-color in fallback pixels
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF00FF88u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets later background shorthand override earlier background-color in fallback pixels")
val html = "<html><body style='background-color: rebeccapurple; background: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background-color override earlier background shorthand in fallback pixels

- lets later background-color override earlier background shorthand in fallback pixels
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF663399u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets later background-color override earlier background shorthand in fallback pixels")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserRenderer HTML rendering.
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 130 |
| Active scenarios | 130 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b9d1f8f63e6301b71ac0db30934137f1c913c37ca494e75d18671a1000b19a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b9d1f8f63e6301b71ac0db30934137f1c913c37ca494e75d18671a1000b19a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b9d1f8f63e6301b71ac0db30934137f1c913c37ca494e75d18671a1000b19a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 42 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders inline background blocks without producing a blank frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders style block CSS without hanging' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders arbitrary non-fixture CSS through layout and paint instead of fill-only fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

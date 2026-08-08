# Chromium Vs Simple Text Specification

> <details>

<!-- sdn-diagram:id=chromium_vs_simple_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chromium_vs_simple_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chromium_vs_simple_text_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chromium_vs_simple_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chromium Vs Simple Text Specification

## Scenarios

### Chromium vs Simple — simple text

#### electron capture file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(electron_path)).to_equal(true)
```

</details>

#### Simple renderer produces non-empty pixels

1. var html = rt file read text
2. var pixels = simple web render html to pixels
   - Expected: pixels.len() equals `W * H`
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var html = rt_file_read_text(html_fixture_path)
var pixels = simple_web_render_html_to_pixels(html, W, H)
expect(pixels.len()).to_equal(W * H)
var non_white = 0
var i = 0
while i < pixels.len():
    if pixels[i] != 0xFFFFFFFFu32:
        non_white = non_white + 1
    i = i + 1
print("simple non-white pixels: " + non_white.to_text())
expect(non_white).to_be_greater_than(0)
```

</details>

#### pixel diff diagnostic — simple text

1. var html = rt file read text
2. var chrome = load electron argb
3. var simple = simple web render html to pixels
4. var d = diff pixels
5. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var html = rt_file_read_text(html_fixture_path)
var chrome = load_electron_argb(electron_path)
var simple = simple_web_render_html_to_pixels(html, W, H)
var d = diff_pixels("simple_text", chrome, simple, W, H)
print("differing_pixels=" + d.to_text())
expect(d).to_be_greater_than(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/pixel_compare/chromium_vs_simple_text_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chromium vs Simple — simple text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

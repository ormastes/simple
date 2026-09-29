# Pseudo Text Wpt Specification

> <details>

<!-- sdn-diagram:id=pseudo_text_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pseudo_text_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pseudo_text_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pseudo_text_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pseudo Text Wpt Specification

## Scenarios

### WPT-derived pseudo-element and text shaping

#### before pseudo-element content

#### renders before pseudo-element content text on empty div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #2563eb; } div::before { content: 'Hello'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF2563EBu32)).to_equal(true)
```

</details>

#### renders before pseudo-element on empty element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #16a34a; } div::before { content: 'Generated'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF16A34Au32)).to_equal(true)
```

</details>

#### renders before pseudo-element attr content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #2563eb; font-size: 8px; } div::before { content: attr(data-label); }"
val body = "<div data-label='ABC'></div>"
expect(_pixel_count(style, body, 0xFF2563EBu32)).to_equal(96)
```

</details>

#### after pseudo-element content

#### renders after pseudo-element content text on empty div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #dc2626; } div::after { content: 'Suffix'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFFDC2626u32)).to_equal(true)
```

</details>

#### renders after pseudo-element on empty element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #7c3aed; } div::after { content: 'Only'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF7C3AEDu32)).to_equal(true)
```

</details>

#### renders after pseudo-element attr content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #dc2626; font-size: 8px; } div::after { content: attr(data-label); }"
val body = "<div data-label='XY'></div>"
expect(_pixel_count(style, body, 0xFFDC2626u32)).to_equal(64)
```

</details>

#### keeps missing attr pseudo content empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #dc2626; font-size: 8px; } div::after { content: attr(data-label); }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFFDC2626u32)).to_equal(false)
```

</details>

#### renders both before and after pseudo-elements on empty div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #0891b2; } div::before { content: 'A'; } div::after { content: 'Z'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF0891B2u32)).to_equal(true)
```

</details>

#### does not render generated content for display none element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { display: none; color: #0891b2; } div::before { content: 'Hidden'; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF0891B2u32)).to_equal(false)
```

</details>

#### does not render generated content when pseudo display is none

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { color: #0891b2; } div::before { content: 'Hidden'; display: none; }"
val body = "<div></div>"
expect(_renders_color(style, body, 0xFF0891B2u32)).to_equal(false)
```

</details>

#### text-overflow ellipsis

#### truncates overflowing text with ellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trunc_style = "div { width: 40px; overflow: hidden; white-space: nowrap; text-overflow: ellipsis; color: #0f766e; font-size: 8px; }"
val no_trunc_style = "div { width: 40px; color: #0f766e; font-size: 8px; }"
val body = "<div>ThisIsAVeryLongWordThatOverflows</div>"
val trunc_px = _pixel_count(trunc_style, body, 0xFF0F766Eu32)
val no_trunc_px = _pixel_count(no_trunc_style, body, 0xFF0F766Eu32)
expect(trunc_px).to_be_less_than(no_trunc_px)
```

</details>

#### word-break and overflow-wrap

#### break-all wraps long word onto second line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { width: 40px; word-break: break-all; color: #4338ca; font-size: 8px; }"
val body = "<div>ABCDEFGHIJKLMNOPQRST</div>"
val second_row = 8 + 4 + 2
expect(_has_color_at_row(style, body, 0xFF4338CAu32, second_row)).to_equal(true)
```

</details>

#### overflow-wrap break-word wraps long word onto second line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { width: 40px; overflow-wrap: break-word; color: #9333ea; font-size: 8px; }"
val body = "<div>ABCDEFGHIJKLMNOPQRST</div>"
val second_row = 8 + 4 + 2
expect(_has_color_at_row(style, body, 0xFF9333EAu32, second_row)).to_equal(true)
```

</details>

#### text-align fallback rendering

#### centers short text within the fallback block width

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { width: 40px; text-align: center; color: #ea580c; font-size: 8px; }"
val body = "<div>AB</div>"
expect(_has_color_at(style, body, 0xFFEA580Cu32, 15, 2)).to_equal(true)
expect(_has_color_at(style, body, 0xFFEA580Cu32, 0, 2)).to_equal(false)
```

</details>

#### right aligns short text within the fallback block width

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div { width: 40px; text-align: right; color: #0d9488; font-size: 8px; }"
val body = "<div>AB</div>"
expect(_has_color_at(style, body, 0xFF0D9488u32, 30, 2)).to_equal(true)
expect(_has_color_at(style, body, 0xFF0D9488u32, 0, 2)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/pseudo_text_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived pseudo-element and text shaping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

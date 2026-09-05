# Wordart Specification

> Tests covering wordart: plain preset, wordart: outline preset, wordart: shadow preset, wordart: gradient preset, wordart: html rendering, wordart: preset listing and validation, wordart: content escaping, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wordart Specification

## Scenarios

### wordart: plain preset

#### renders exactly one <text element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "plain", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
val text_count = svg.split("<text").len() - 1
expect(text_count).to_equal(1)
```

</details>

#### has no stroke attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "plain", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
assert_false(svg.contains("stroke"))
```

</details>

### wordart: outline preset

#### contains a <text element, the fill hex, and a stroke

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "outline", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
expect(svg).to_contain("<text")
expect(svg).to_contain("#c00000")
expect(svg).to_contain("stroke")
```

</details>

### wordart: shadow preset

#### renders exactly two <text elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "shadow", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
val text_count = svg.split("<text").len() - 1
expect(text_count).to_equal(2)
```

</details>

#### includes the gray #888888 shadow copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "shadow", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
expect(svg).to_contain("#888888")
```

</details>

### wordart: gradient preset

#### defines a linearGradient and references it via url(#

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "gradient", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
expect(svg).to_contain("<linearGradient")
expect(svg).to_contain("url(#")
```

</details>

### wordart: html rendering

#### contains the content and a color style

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "outline", "#c00000", 10, 20, 48)
val html = wordart_to_html(art)
expect(html).to_contain("Big Sale")
expect(html).to_contain("color:")
```

</details>

### wordart: preset listing and validation

#### lists exactly four preset names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = wordart_preset_names()
expect(names.len()).to_equal(4)
```

</details>

#### validates a known preset name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(wordart_is_valid_preset("outline"))
```

</details>

#### rejects an unknown preset name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_false(wordart_is_valid_preset("bogus"))
```

</details>

### wordart: content escaping

#### escapes < in the content to &lt;

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("A < B", "plain", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
expect(svg).to_contain("A &lt; B")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the shadow text-element count ground truth

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = wordart_new("Big Sale", "shadow", "#c00000", 10, 20, 48)
val svg = wordart_to_svg(art)
val text_count = svg.split("<text").len() - 1
# Probe verified live: asserting 3 <text elements (one more
# than shadow's real count) failed with "expected 2 to equal
# 3", confirming the harness executes this assertion. Correct
# ground truth: shadow renders exactly 2 <text elements.
expect(text_count).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/wordart_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wordart: plain preset, wordart: outline preset, wordart: shadow preset, wordart: gradient preset, wordart: html rendering, wordart: preset listing and validation, wordart: content escaping, deliberate-fail probe (must stay green).
- wordart: plain preset
- wordart: outline preset
- wordart: shadow preset
- wordart: gradient preset
- wordart: html rendering
- wordart: preset listing and validation
- wordart: content escaping
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Glyph Specification

> <details>

<!-- sdn-diagram:id=glyph_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glyph_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glyph_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glyph_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glyph Specification

## Scenarios

### Engine2D glyph data

#### keeps uppercase glyph rows on the packed fast path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(glyph_data("A")).to_equal([0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001])
expect(glyph_data("Z")).to_equal([0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0b11111])
```

</details>

#### keeps lowercase glyph rows on the packed fast path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(glyph_data("a")).to_equal([0b00000, 0b00000, 0b01110, 0b00001, 0b01111, 0b10001, 0b01111])
expect(glyph_data("z")).to_equal([0b00000, 0b00000, 0b11111, 0b00010, 0b00100, 0b01000, 0b11111])
```

</details>

#### keeps digit glyph rows on the packed fast path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(glyph_data("0")).to_equal([0b01110, 0b10001, 0b10011, 0b10101, 0b11001, 0b10001, 0b01110])
expect(glyph_data("9")).to_equal([0b01110, 0b10001, 0b10001, 0b01111, 0b00001, 0b00001, 0b01110])
```

</details>

#### keeps punctuation and unknown fallback behavior unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(glyph_data(" ")).to_equal([0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000])
expect(glyph_data("?")).to_equal([0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0b00000, 0b00100])
expect(glyph_data("\"")).to_equal([0b01010, 0b01010, 0b01010, 0b00000, 0b00000, 0b00000, 0b00000])
expect(glyph_data("\\")).to_equal([0b10000, 0b01000, 0b01000, 0b00100, 0b00010, 0b00010, 0b00001])
expect(glyph_data("|")).to_equal([0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100])
expect(glyph_data("~")).to_equal([0b00000, 0b00000, 0b01000, 0b10101, 0b00010, 0b00000, 0b00000])
expect(glyph_data("")).to_equal([0b11111, 0b11111, 0b11111, 0b11111, 0b11111, 0b11111, 0b11111])
expect(glyph_data("\n")).to_equal([0b11111, 0b11111, 0b11111, 0b11111, 0b11111, 0b11111, 0b11111])
expect(glyph_data("AA")).to_equal([0b11111, 0b11111, 0b11111, 0b11111, 0b11111, 0b11111, 0b11111])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/glyph_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D glyph data

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

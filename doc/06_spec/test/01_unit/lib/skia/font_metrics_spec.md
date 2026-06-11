# Skia Font Metrics Specification

> Tests for parse_hhea, parse_os2, parse_post — OpenType per-font metric extractors used by the text layout engine for baseline alignment and line spacing.

<!-- sdn-diagram:id=font_metrics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=font_metrics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

font_metrics_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=font_metrics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Font Metrics Specification

Tests for parse_hhea, parse_os2, parse_post — OpenType per-font metric extractors used by the text layout engine for baseline alignment and line spacing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-FM-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/font_metrics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for parse_hhea, parse_os2, parse_post — OpenType per-font metric
extractors used by the text layout engine for baseline alignment and
line spacing.

## Scenarios

### font_metrics

#### parse_hhea: empty blob returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = parse_hhea(empty)
expect(result).to_be_nil()
```

</details>

#### parse_hhea: 36-byte blob with ascent=1800, descent=-400, line_gap=200 parses correctly

1.  set u32 be
2.  set i16 be
3.  set i16 be
4.  set i16 be
5.  set u16 be
6.  set u16 be
   - Expected: metrics.ascent equals `1800`
   - Expected: metrics.descent equals `-400`
   - Expected: metrics.line_gap equals `200`
   - Expected: metrics.advance_width_max equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _zeros(36)
# version 0x00010000
_set_u32_be(buf, 0, 65536)
_set_i16_be(buf, 4, 1800)
_set_i16_be(buf, 6, -400)
_set_i16_be(buf, 8, 200)
_set_u16_be(buf, 10, 2048)
_set_u16_be(buf, 34, 512)
val result = parse_hhea(buf)
val metrics = result.unwrap()
expect(metrics.ascent).to_equal(1800)
expect(metrics.descent).to_equal(-400)
expect(metrics.line_gap).to_equal(200)
expect(metrics.advance_width_max).to_equal(2048)
```

</details>

#### parse_hhea: num_long_hor_metrics read from offset 34

1.  set u32 be
2.  set u16 be
   - Expected: metrics.num_long_hor_metrics equals `1337`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _zeros(36)
_set_u32_be(buf, 0, 65536)
_set_u16_be(buf, 34, 1337)
val result = parse_hhea(buf)
val metrics = result.unwrap()
expect(metrics.num_long_hor_metrics).to_equal(1337)
```

</details>

#### parse_os2: version 0 blob x_height = 0 (field not present)

1.  set u16 be
2.  set i16 be
3.  set i16 be
   - Expected: metrics.x_height equals `0`
   - Expected: metrics.cap_height equals `0`
   - Expected: metrics.typo_ascent equals `1600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _zeros(78)
_set_u16_be(buf, 0, 0)
_set_i16_be(buf, 68, 1600)
_set_i16_be(buf, 70, -400)
val result = parse_os2(buf)
val metrics = result.unwrap()
expect(metrics.x_height).to_equal(0)
expect(metrics.cap_height).to_equal(0)
expect(metrics.typo_ascent).to_equal(1600)
```

</details>

#### parse_os2: version 2 blob with sxHeight=500 returns 500

1.  set u16 be
2.  set i16 be
3.  set i16 be
   - Expected: metrics.x_height equals `500`
   - Expected: metrics.cap_height equals `700`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _zeros(96)
_set_u16_be(buf, 0, 2)
_set_i16_be(buf, 86, 500)
_set_i16_be(buf, 88, 700)
val result = parse_os2(buf)
val metrics = result.unwrap()
expect(metrics.x_height).to_equal(500)
expect(metrics.cap_height).to_equal(700)
```

</details>

#### parse_post: reads italic_angle as Fixed 16.16

1.  set u32 be
   - Expected: close is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _zeros(32)
# italic_angle = -12.0 => -12 * 65536 = -786432
# Encoded as u32: 4294967296 - 786432 = 4294180864
_set_u32_be(buf, 4, 4294180864)
val result = parse_post(buf)
val metrics = result.unwrap()
val delta = metrics.italic_angle - (-12.0)
val abs_delta = if delta < 0.0: -delta else: delta
val close = abs_delta < 1e-6
expect(close).to_equal(true)
```

</details>

#### parse_post: is_fixed_pitch from offset 12

1.  set u32 be
   - Expected: metrics.is_fixed_pitch is true
2.  set u32 be
   - Expected: metrics2.is_fixed_pitch is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _zeros(32)
_set_u32_be(buf, 12, 1)
val result = parse_post(buf)
val metrics = result.unwrap()
expect(metrics.is_fixed_pitch).to_equal(true)

val buf2 = _zeros(32)
_set_u32_be(buf2, 12, 0)
val result2 = parse_post(buf2)
val metrics2 = result2.unwrap()
expect(metrics2.is_fixed_pitch).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

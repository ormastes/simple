# Css Ext Specification

> <details>

<!-- sdn-diagram:id=css_ext_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=css_ext_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

css_ext_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=css_ext_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Ext Specification

## Scenarios

### CSS ext — float / clear parsers

#### parses the CSS 2.1 float keyword set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_float_keyword("none") == 0).to_be_true()
expect(parse_float_keyword("left") == 1).to_be_true()
expect(parse_float_keyword("right") == 2).to_be_true()
```

</details>

#### parses the CSS Logical Properties float keywords

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_float_keyword("inline-start") == 3).to_be_true()
expect(parse_float_keyword("inline-end") == 4).to_be_true()
```

</details>

#### returns -1 for unknown float values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_float_keyword("wibble") == -1).to_be_true()
expect(parse_float_keyword("") == -1).to_be_true()
```

</details>

#### parses the full clear keyword set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_clear_keyword("none") == 0).to_be_true()
expect(parse_clear_keyword("left") == 1).to_be_true()
expect(parse_clear_keyword("right") == 2).to_be_true()
expect(parse_clear_keyword("both") == 3).to_be_true()
expect(parse_clear_keyword("inline-start") == 4).to_be_true()
expect(parse_clear_keyword("inline-end") == 5).to_be_true()
```

</details>

#### returns -1 for unknown clear values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_clear_keyword("nope") == -1).to_be_true()
```

</details>

### CSS ext — BoxShadow

#### BoxShadow.none produces an invisible shadow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shadow = BoxShadow.none()
expect(not shadow.is_visible()).to_be_true()
expect(shadow.inset == false).to_be_true()
```

</details>

#### BoxShadow.new captures offsets / blur / spread / colour

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shadow = BoxShadow.new(4, 6, 8, 2, 0xFF112233, false)
expect(shadow.offset_x_px == 4).to_be_true()
expect(shadow.offset_y_px == 6).to_be_true()
expect(shadow.blur_px == 8).to_be_true()
expect(shadow.spread_px == 2).to_be_true()
expect(shadow.is_visible()).to_be_true()
```

</details>

#### fully transparent shadow is not visible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shadow = BoxShadow.new(4, 4, 0, 0, 0x00112233, false)
expect(not shadow.is_visible()).to_be_true()
```

</details>

#### inset flag is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shadow = BoxShadow.new(1, 1, 2, 0, 0xFF000000, true)
expect(shadow.inset == true).to_be_true()
```

</details>

### CSS ext — Outline

#### parses the full outline-style keyword set

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_outline_style("none") == 0).to_be_true()
expect(parse_outline_style("hidden") == 1).to_be_true()
expect(parse_outline_style("dotted") == 2).to_be_true()
expect(parse_outline_style("dashed") == 3).to_be_true()
expect(parse_outline_style("solid") == 4).to_be_true()
expect(parse_outline_style("double") == 5).to_be_true()
expect(parse_outline_style("groove") == 6).to_be_true()
expect(parse_outline_style("ridge") == 7).to_be_true()
expect(parse_outline_style("inset") == 8).to_be_true()
expect(parse_outline_style("outset") == 9).to_be_true()
```

</details>

#### returns -1 for unknown outline-style

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_outline_style("") == -1).to_be_true()
expect(parse_outline_style("wobble") == -1).to_be_true()
```

</details>

#### Outline.none is invisible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = Outline.none()
expect(not o.is_visible()).to_be_true()
```

</details>

#### Outline.new captures width / style / colour / offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = Outline.new(3, 4, 0xFFFF0000, 2)
expect(o.width_px == 3).to_be_true()
expect(o.offset_px == 2).to_be_true()
expect(o.is_visible()).to_be_true()
```

</details>

#### outline-style: none suppresses the outline even with width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = Outline.new(5, 0, 0xFFFFFFFF, 0)
expect(not o.is_visible()).to_be_true()
```

</details>

#### zero width outline is invisible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = Outline.new(0, 4, 0xFFFFFFFF, 0)
expect(not o.is_visible()).to_be_true()
```

</details>

#### transparent colour outline is invisible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = Outline.new(2, 4, 0x00FFFFFF, 0)
expect(not o.is_visible()).to_be_true()
```

</details>

### CSS ext — calc() resolver

#### calc_apply handles the four operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = calc_apply(CALC_OP_ADD, 10, 5)
expect(a.ok).to_be_true()
expect(a.pixels == 15).to_be_true()
val s = calc_apply(CALC_OP_SUB, 10, 5)
expect(s.pixels == 5).to_be_true()
val m = calc_apply(CALC_OP_MUL, 10, 5)
expect(m.pixels == 50).to_be_true()
val d = calc_apply(CALC_OP_DIV, 10, 5)
expect(d.pixels == 2).to_be_true()
```

</details>

#### calc_apply reports divide-by-zero as a failed CalcValue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dz = calc_apply(CALC_OP_DIV, 10, 0)
expect(not dz.ok).to_be_true()
```

</details>

#### calc_resolve evaluates a lone value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = calc_resolve([42], [])
expect(r.ok).to_be_true()
expect(r.pixels == 42).to_be_true()
```

</details>

#### calc_resolve honours operator precedence (2 + 3 * 4 == 14)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = calc_resolve([2, 3, 4], [CALC_OP_ADD, CALC_OP_MUL])
expect(r.ok).to_be_true()
expect(r.pixels == 14).to_be_true()
```

</details>

#### calc_resolve walks + / - left to right (10 - 3 + 2 == 9)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = calc_resolve([10, 3, 2], [CALC_OP_SUB, CALC_OP_ADD])
expect(r.ok).to_be_true()
expect(r.pixels == 9).to_be_true()
```

</details>

#### calc_resolve evaluates chained multiplications

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = calc_resolve([2, 3, 4], [CALC_OP_MUL, CALC_OP_MUL])
expect(r.ok).to_be_true()
expect(r.pixels == 24).to_be_true()
```

</details>

#### calc_resolve propagates divide-by-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = calc_resolve([10, 0], [CALC_OP_DIV])
expect(not r.ok).to_be_true()
```

</details>

#### calc_resolve rejects mismatched operand / operator counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = calc_resolve([1, 2], [])
expect(not r.ok).to_be_true()
```

</details>

#### calc_resolve rejects empty operand list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = calc_resolve([], [])
expect(not r.ok).to_be_true()
```

</details>

### CSS ext — M8 milestone marker

#### marker reports the milestone number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(m8_marker() == 8).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/css_ext_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CSS ext — float / clear parsers
- CSS ext — BoxShadow
- CSS ext — Outline
- CSS ext — calc() resolver
- CSS ext — M8 milestone marker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

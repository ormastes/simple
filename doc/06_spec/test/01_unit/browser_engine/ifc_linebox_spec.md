# Ifc Linebox Specification

> <details>

<!-- sdn-diagram:id=ifc_linebox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ifc_linebox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ifc_linebox_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ifc_linebox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ifc Linebox Specification

## Scenarios

### IFC LineBox line break

#### AC-4: short text fits on one line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html("<span>Hi</span>")
val count = _line_count(box_)
expect(count).to_equal(1)
```

</details>

#### AC-4: long text wraps to multiple lines in narrow container

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 200px container, long word sequence should wrap
val box_ = _layout_inline_html("<span>word1 word2 word3 word4 word5 word6 word7 word8 word9 word10</span>")
val count = _line_count(box_)
expect(count).to_be_greater_than(1)
```

</details>

#### AC-4: total height grows with more lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box1 = _layout_inline_html("<span>short</span>")
val box2 = _layout_inline_html("<span>word1 word2 word3 word4 word5 word6 word7 word8 word9 word10</span>")
val h1 = _total_height(box1)
val h2 = _total_height(box2)
expect(h2).to_be_greater_than(h1)
```

</details>

### IFC LineBox baseline

#### AC-4: line box has non-negative baseline offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html("<span>text</span>")
val line = _first_line(box_)
expect(line.baseline).to_be_greater_than(-1)
```

</details>

#### AC-4: line box width does not exceed container width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html("<span>text that fits</span>")
val line = _first_line(box_)
expect(line.width).to_be_less_than(201)
```

</details>

#### AC-4: normal long words stay on one overflowing inline line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html_width("<div style=\"word-break:normal;overflow-wrap:normal\">supercalifragilistic</div>", 40)
expect(_line_count(box_)).to_equal(1)
val line = _first_line(box_)
expect(line.fragments[0].width).to_be_greater_than(40)
```

</details>

#### AC-4: word-break break-all splits oversized first inline token

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html_width("<div style=\"word-break:break-all\">supercalifragilistic</div>", 40)
expect(_line_count(box_)).to_be_greater_than(1)
val line = _first_line(box_)
expect(line.fragments[0].width).to_be_less_than(41)
```

</details>

#### AC-4: overflow-wrap break-word splits oversized first inline token

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html_width("<div style=\"overflow-wrap:break-word\">supercalifragilistic</div>", 40)
expect(_line_count(box_)).to_be_greater_than(1)
val line = _first_line(box_)
expect(line.fragments[0].width).to_be_less_than(41)
```

</details>

### IFC LineBox text-align

#### AC-4: left-aligned fragment starts at x=0 (default)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html("<span>left</span>")
val line = _first_line(box_)
val frag = line.fragments[0]
expect(frag.x).to_equal(0)
```

</details>

#### AC-4: center-aligned line fragment x is positive for short text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _layout_inline_html("<div style=\"text-align:center;width:200px\">hi</div>")
val line = _first_line(box_)
val frag = line.fragments[0]
expect(frag.x).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/ifc_linebox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IFC LineBox line break
- IFC LineBox baseline
- IFC LineBox text-align

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

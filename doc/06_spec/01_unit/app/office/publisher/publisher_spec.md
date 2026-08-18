# Publisher Specification

> Tests covering publisher page layout: frame construction, publisher page layout: text flow and overflow, publisher page layout: HTML rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Publisher Specification

## Scenarios

### publisher page layout: frame construction

#### counts frames added to the page

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _linked_page()
expect(page_frame_count(page)).to_equal(2)
```

</details>

#### starts with empty frame text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _linked_page()
expect(frame_text(page, "f1")).to_equal("")
expect(frame_text(page, "f2")).to_equal("")
```

</details>

### publisher page layout: text flow and overflow

#### fills frame f1 with exactly 3 words up to its char capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(frame_text(page, "f1")).to_equal("The cat sat")
```

</details>

#### overflows the remaining words into linked frame f2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(frame_text(page, "f2")).to_equal("on the mat")
```

</details>

#### never splits a word across frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(frame_text(page, "f1").contains("o")).to_be(false)
```

</details>

#### preserves frame count after flowing text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(page_frame_count(page)).to_equal(2)
```

</details>

### publisher page layout: HTML rendering

#### renders a positioned div for each frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_contain("id=\"f1\"")
expect(html).to_contain("id=\"f2\"")
```

</details>

#### positions frames with absolute left/top/width/height styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_contain("position:absolute;left:0px;top:0px;width:66px;height:16px;")
expect(html).to_contain("position:absolute;left:0px;top:20px;width:100px;height:32px;")
```

</details>

#### contains both frames' flowed text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_contain("The cat sat")
expect(html).to_contain("on the mat")
```

</details>

#### wraps the page in a relatively-positioned container

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_start_with("<div class=\"pub-page\"")
expect(html).to_contain("position:relative;width:200px;height:100px;")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks capacity math holds (fixed, was deliberately wrong)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
# Probe verified live: asserting "The cat sat on" (4 words) here
# failed with "expected The cat sat to equal The cat sat on",
# confirming the harness executes this assertion. Capacity math
# (11 chars) only admits 3 words in f1, so the correct assertion
# is the 3-word split below.
expect(frame_text(page, "f1")).to_equal("The cat sat")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/publisher_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering publisher page layout: frame construction, publisher page layout: text flow and overflow, publisher page layout: HTML rendering, deliberate-fail probe (must stay green).
- publisher page layout: frame construction
- publisher page layout: text flow and overflow
- publisher page layout: HTML rendering
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

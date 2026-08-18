# Wrap Specification

> Tests covering publisher wrap: narrowed lines beside the object, publisher wrap: full-width line below the object, publisher wrap: line count, publisher wrap: html rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wrap Specification

## Scenarios

### publisher wrap: narrowed lines beside the object

#### narrows line 0 to the space right of the object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
expect(lines[0]).to_equal("aaaa bbbb")
```

</details>

#### narrows line 1 to the space right of the object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
expect(lines[1]).to_equal("cccc dddd")
```

</details>

### publisher wrap: full-width line below the object

#### uses the full frame width once past the object's row-band

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
expect(lines[2]).to_equal("eeee ffff gggg hhhh")
```

</details>

### publisher wrap: line count

#### produces exactly 3 lines for the full content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = wrap_line_count(0, 0, 120, 48, CONTENT, _obj())
expect(count).to_equal(3)
```

</details>

### publisher wrap: html rendering

#### includes a positioned float div for the object

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wrap_render_html(0, 0, 120, 48, CONTENT, _obj())
expect(html).to_contain("pub-float")
expect(html).to_contain("width:60px")
expect(html).to_contain("height:32px")
```

</details>

#### includes the text region div with the wrapped lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wrap_render_html(0, 0, 120, 48, CONTENT, _obj())
expect(html).to_contain("pub-wrap-text")
expect(html).to_contain("aaaa bbbb")
expect(html).to_contain("eeee ffff gggg hhhh")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the hand-computed narrowed-vs-full split ground truth

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
# Probe verified live: asserting line 0 equals the full-width
# line's content ("eeee ffff gggg hhhh") failed with a
# mismatch, confirming the harness executes this assertion.
# Correct ground truth: line 0 is narrowed to "aaaa bbbb".
expect(lines[0]).to_equal("aaaa bbbb")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/wrap_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering publisher wrap: narrowed lines beside the object, publisher wrap: full-width line below the object, publisher wrap: line count, publisher wrap: html rendering, deliberate-fail probe (must stay green).
- publisher wrap: narrowed lines beside the object
- publisher wrap: full-width line below the object
- publisher wrap: line count
- publisher wrap: html rendering
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

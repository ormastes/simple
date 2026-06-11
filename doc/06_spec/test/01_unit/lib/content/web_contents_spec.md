# Web Contents Specification

> <details>

<!-- sdn-diagram:id=web_contents_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_contents_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_contents_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_contents_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Contents Specification

## Scenarios

### WebContents.new

#### gives correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wc = WebContents.new(42, _rect())
expect wc.id to_equal 42
```

</details>

#### gives correct viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wc = WebContents.new(1, _rect())
expect wc.viewport.right to_equal 800.0
```

</details>

#### main_frame_surface has matching client_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wc = WebContents.new(7, _rect())
expect wc.main_frame_surface.frame_sink_id.client_id to_equal 7
```

</details>

#### main_frame_surface sink_id is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wc = WebContents.new(3, _rect())
expect wc.main_frame_surface.frame_sink_id.sink_id to_equal 1
```

</details>

### WebContents mutations

#### navigate updates url

1. var wc = WebContents new
2. wc navigate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wc = WebContents.new(1, _rect())
wc.navigate("https://example.com")
expect wc.url to_equal "https://example.com"
```

</details>

#### set_title updates title

1. var wc = WebContents new
2. wc set title


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wc = WebContents.new(1, _rect())
wc.set_title("Hello")
expect wc.title to_equal "Hello"
```

</details>

#### update_paint populates last_paint

1. var wc = WebContents new
2. wc update paint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wc = WebContents.new(1, _rect())
val art = PaintArtifact.empty()
wc.update_paint(art)
val has_paint = wc.last_paint.is_some()
expect has_paint to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/content/web_contents_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebContents.new
- WebContents mutations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

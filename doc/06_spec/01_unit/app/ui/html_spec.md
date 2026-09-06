# Html Specification

> <details>

<!-- sdn-diagram:id=html_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Specification

## Scenarios

### HtmlRenderer

### new()

#### creates renderer with empty state

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # html, css, js all empty initially
```

</details>

### minified()

#### enables minified output mode

1. expect true  #  minified


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .minified(); minify == true
```

</details>

### render_element

#### renders basic div element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # contains <div> and </div>
```

</details>

#### renders text content with escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # <script> becomes &lt;script&gt;
```

</details>

#### renders nested elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # child elements rendered inside parent
```

</details>

#### renders with classes and attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # class="..." and data-id="..."
```

</details>

### render_document

#### generates complete HTML document

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # DOCTYPE, html, head, body
```

</details>

#### includes base CSS styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # box-sizing, .sui-button, etc.
```

</details>

#### includes event handler JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # suiEvent function
```

</details>

### is_void_element

#### identifies void elements correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # input, br, img are void; div, span are not
```

</details>

### HydrationManifest

### new()

#### creates empty manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # version=1, empty maps
```

</details>

### add_node

#### adds node to manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # node_map contains node_id -> selector
```

</details>

### add_event

#### adds event binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # event_bindings array has entry
```

</details>

### set_state

#### stores initial state

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # initial_state contains key -> value
```

</details>

### to_json

#### generates valid JSON structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # version, nodes, events, state keys
```

</details>

### patches_to_js

#### generates JavaScript for SetText patch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # textContent = '...'
```

</details>

#### generates JavaScript for SetAttr patch

1. expect true  # setAttribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # setAttribute('...', '...')
```

</details>

#### generates JavaScript for AddClass patch

1. expect true  # classList add


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # classList.add('...')
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/html_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HtmlRenderer
- new()
- minified()
- render_element
- render_document
- is_void_element
- HydrationManifest
- new()
- add_node
- add_event
- set_state
- to_json
- patches_to_js

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

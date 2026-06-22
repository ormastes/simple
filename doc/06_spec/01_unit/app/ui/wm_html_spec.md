# Wm Html Specification

> <details>

<!-- sdn-diagram:id=wm_html_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_html_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_html_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_html_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Html Specification

## Scenarios

### generate_wm_js route

#### connects the WM boot script to the routed UI websocket

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val js = generate_wm_js(3333)
expect(js).to_contain("ws://localhost:")
expect(js).to_contain("3333")
expect(js).to_contain("/ui/ws")
expect(js).to_contain("new SimpleWindowManager()")
```

</details>

### desktop glass CSS

#### keeps tablet widths on the desktop layout path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_css("glass_dark")
expect(css).to_contain(".widget-menubar::before")
expect(css).not_to_contain("@media (max-width: 900px)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/wm_html_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- generate_wm_js route
- desktop glass CSS

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

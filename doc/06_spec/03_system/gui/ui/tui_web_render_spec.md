# Tui Web Render Specification

> <details>

<!-- sdn-diagram:id=tui_web_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_web_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_web_render_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_web_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Web Render Specification

## Scenarios

### TUI web render portable smoke

#### records backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = "tui_web"
expect(backend).to_equal("tui_web")
```

</details>

#### records fixture path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = "test/fixtures/ui/test_app.ui.sdn"
expect(fixture).to_end_with(".ui.sdn")
```

</details>

#### records rendered surface expectation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = "html"
expect(surface).to_equal("html")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/tui_web_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TUI web render portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

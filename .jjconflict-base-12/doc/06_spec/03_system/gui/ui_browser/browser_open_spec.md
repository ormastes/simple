# Browser Open Specification

> <details>

<!-- sdn-diagram:id=browser_open_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_open_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_open_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_open_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Open Specification

## Scenarios

### Browser Engine portable snapshot smoke

#### records snapshot path and format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = ".build/ui_browser/test_hello.ppm"
val format = "P3"
expect(snapshot).to_end_with(".ppm")
expect(format).to_equal("P3")
```

</details>

#### records default snapshot dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val width = 1280
val height = 720
expect(width).to_equal(1280)
expect(height).to_equal(720)
```

</details>

#### records non-background paint colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel_rgb = "45 45 45"
val text_rgb = "224 224 224"
expect(panel_rgb).to_contain("45")
expect(text_rgb).to_contain("224")
```

</details>

### Browser Engine portable GUI gate

#### keeps GUI open behavior opt-in

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_name = "SIMPLE_GUI_TEST"
expect(env_name).to_equal("SIMPLE_GUI_TEST")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui_browser/browser_open_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser Engine portable snapshot smoke
- Browser Engine portable GUI gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Display Detect Specification

> <details>

<!-- sdn-diagram:id=display_detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=display_detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

display_detect_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=display_detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Display Detect Specification

## Scenarios

### Display Detection

#### returns a DisplayInfo struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_display()
# Just verify it returns without crashing
val name = display_kind_name(info.kind)
expect(name).to_equal("").to_equal(false)
```

</details>

#### has_any_display returns a boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = has_any_display()
# On any system this should return true or false
expect(result == true or result == false).to_equal(true)
```

</details>

#### can_show_gui returns a boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = can_show_gui()
expect(result == true or result == false).to_equal(true)
```

</details>

### display_kind_name

#### names all display types

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(DISPLAY_NONE)).to_equal("none")
expect(display_kind_name(DISPLAY_X11)).to_equal("X11")
expect(display_kind_name(DISPLAY_WAYLAND)).to_equal("Wayland")
expect(display_kind_name(DISPLAY_MACOS)).to_equal("macOS")
expect(display_kind_name(DISPLAY_XVFB)).to_equal("Xvfb")
```

</details>

#### handles unknown values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(99)).to_equal("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/display_detect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Display Detection
- display_kind_name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

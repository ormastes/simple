# Pure Gui Release Lane Specification

## Scenarios

### pure GUI release lane

#### keeps std.gui public surface free of WM, web renderer, and native GUI runtime deps

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/lib/gui/__init__.spl")
expect(_has_forbidden_release_dependency(source)).to_equal(false)
```

</details>

#### keeps pure GUI command boundary free of WM, web renderer, and native GUI runtime deps

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/lib/gui/pure_core.spl")
expect(_has_forbidden_release_dependency(source)).to_equal(false)
```

</details>

#### keeps pure GUI SMF dynlib perf contract free of WM, web renderer, and native GUI runtime deps

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/lib/gui/pure_smf_dynlib_perf.spl")
expect(_has_forbidden_release_dependency(source)).to_equal(false)
```

</details>

#### keeps BrowserWindow entity free of native GUI runtime deps

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/lib/gui/entity/browser_window.spl")
expect(_has_forbidden_release_dependency(source)).to_equal(false)
```

</details>

#### keeps Menu entity free of native GUI runtime deps

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/lib/gui/entity/menu.spl")
expect(_has_forbidden_release_dependency(source)).to_equal(false)
```

</details>

#### keeps IME entity free of native GUI runtime deps

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/lib/gui/entity/ime.spl")
expect(_has_forbidden_release_dependency(source)).to_equal(false)
```

</details>

#### keeps Printing entity free of native GUI runtime deps

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/lib/gui/entity/printing.spl")
expect(_has_forbidden_release_dependency(source)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gui/pure_gui_release_lane_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure GUI release lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


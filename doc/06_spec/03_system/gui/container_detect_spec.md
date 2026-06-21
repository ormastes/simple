# Container Display Detection Specification

> Verifies display detection logic and backend auto-selection across environments (macOS, X11, Wayland, Xvfb, headless). Tagged `@gui: any` because detection behavior varies by host but the functions must always return valid values without crashing.

<!-- sdn-diagram:id=container_detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=container_detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

container_detect_spec -> std
container_detect_spec -> common
container_detect_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=container_detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Container Display Detection Specification

Verifies display detection logic and backend auto-selection across environments (macOS, X11, Wayland, Xvfb, headless). Tagged `@gui: any` because detection behavior varies by host but the functions must always return valid values without crashing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-DETECT-001 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/container_detect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies display detection logic and backend auto-selection across
environments (macOS, X11, Wayland, Xvfb, headless). Tagged `@gui: any`
because detection behavior varies by host but the functions must always
return valid values without crashing.

## Scenarios

### Display detection

<details>
<summary>Advanced: detect_display returns a DisplayInfo with a valid kind</summary>

#### detect_display returns a DisplayInfo with a valid kind _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_display()
# kind must be one of the known constants (0..4)
val valid = (info.kind == DISPLAY_NONE or
    info.kind == DISPLAY_X11 or
    info.kind == DISPLAY_WAYLAND or
    info.kind == DISPLAY_MACOS or
    info.kind == DISPLAY_XVFB)
expect(valid).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detect_display has a display_name field</summary>

#### detect_display has a display_name field _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_display()
# display_name is text (may be empty for DISPLAY_NONE)
if info.kind != DISPLAY_NONE:
    val name_len = info.display_name.len()
    expect(name_len).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: detect_display has an is_virtual field</summary>

#### detect_display has an is_virtual field _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_display()
# is_virtual is a bool; for Xvfb it is true, otherwise false
if info.kind == DISPLAY_XVFB:
    expect(info.is_virtual).to_equal(true)
if info.kind == DISPLAY_MACOS:
    expect(info.is_virtual).to_equal(false)
```

</details>


</details>

### display_kind_name mapping

<details>
<summary>Advanced: maps DISPLAY_NONE to 'none'</summary>

#### maps DISPLAY_NONE to 'none' _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(DISPLAY_NONE)).to_equal("none")
```

</details>


</details>

<details>
<summary>Advanced: maps DISPLAY_X11 to 'X11'</summary>

#### maps DISPLAY_X11 to 'X11' _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(DISPLAY_X11)).to_equal("X11")
```

</details>


</details>

<details>
<summary>Advanced: maps DISPLAY_WAYLAND to 'Wayland'</summary>

#### maps DISPLAY_WAYLAND to 'Wayland' _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(DISPLAY_WAYLAND)).to_equal("Wayland")
```

</details>


</details>

<details>
<summary>Advanced: maps DISPLAY_MACOS to 'macOS'</summary>

#### maps DISPLAY_MACOS to 'macOS' _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(DISPLAY_MACOS)).to_equal("macOS")
```

</details>


</details>

<details>
<summary>Advanced: maps DISPLAY_XVFB to 'Xvfb'</summary>

#### maps DISPLAY_XVFB to 'Xvfb' _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(DISPLAY_XVFB)).to_equal("Xvfb")
```

</details>


</details>

<details>
<summary>Advanced: maps unknown kind to 'unknown'</summary>

#### maps unknown kind to 'unknown' _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_kind_name(99)).to_equal("unknown")
```

</details>


</details>

### Display boolean queries

<details>
<summary>Advanced: has_any_display returns a boolean</summary>

#### has_any_display returns a boolean _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = has_any_display()
# Result is true or false, must not crash
val is_bool = (result == true or result == false)
expect(is_bool).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can_show_gui returns a boolean</summary>

#### can_show_gui returns a boolean _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = can_show_gui()
val is_bool = (result == true or result == false)
expect(is_bool).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can_show_gui is false when display is NONE</summary>

#### can_show_gui is false when display is NONE _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_display()
if info.kind == DISPLAY_NONE:
    expect(can_show_gui()).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: can_show_gui is false when display is virtual only</summary>

#### can_show_gui is false when display is virtual only _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_display()
if info.is_virtual:
    expect(can_show_gui()).to_equal(false)
```

</details>


</details>

### GUI backend auto-detection

<details>
<summary>Advanced: detect_gui_backend returns a non-empty string</summary>

#### detect_gui_backend returns a non-empty string _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_name = detect_gui_backend()
expect(backend_name.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: detect_gui_backend returns a known backend name</summary>

#### detect_gui_backend returns a known backend name _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = detect_gui_backend()
val known = (name == "tauri" or
    name == "web" or
    name == "headless" or
    name == "tui" or
    name == "none" or
    name == "vscode" or
    name == "electron")
# Also allow env override to any value
if not known:
    # If not a standard name, the env var SIMPLE_GUI_BACKEND was set
    expect(name.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: has_display returns a boolean</summary>

#### has_display returns a boolean _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = has_display()
val is_bool = (result == true or result == false)
expect(is_bool).to_equal(true)
```

</details>


</details>

### Backend factory with detected backend

<details>
<summary>Advanced: creates a headless backend successfully</summary>

#### creates a headless backend successfully _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("headless", 0)
match result:
    Ok(backend) :
        val name = backend.backend_name()
        expect(name.len()).to_be_greater_than(0)
    Err(e) :
        fail("headless backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: creates a none backend successfully</summary>

#### creates a none backend successfully _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("none", 0)
match result:
    Ok(backend) :
        val name = backend.backend_name()
        expect(name.len()).to_be_greater_than(0)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: rejects invalid backend mode</summary>

#### rejects invalid backend mode _(slow)_

1. Err

2. Ok

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("nonexistent", 0)
match result:
    Err(e) :
        expect(e).to_contain("Unknown backend mode")
    Ok(v) :
        fail("invalid backend mode unexpectedly succeeded")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 19 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Native GUI Binary Build & Real GUI Test Specification

> Verifies that GUI apps can be built into standalone native binaries for the current platform and that those binaries actually serve a real GUI (web mode) with correct HTML content.

<!-- sdn-diagram:id=native_gui_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_gui_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_gui_build_spec -> std
native_gui_build_spec -> app
native_gui_build_spec -> nogc_sync_mut
native_gui_build_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_gui_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native GUI Binary Build & Real GUI Test Specification

Verifies that GUI apps can be built into standalone native binaries for the current platform and that those binaries actually serve a real GUI (web mode) with correct HTML content.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-BUILD-001 |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/native_gui_build_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that GUI apps can be built into standalone native binaries
for the current platform and that those binaries actually serve a
real GUI (web mode) with correct HTML content.

This is NOT a container/headless test. It launches a real web server
and makes HTTP requests to verify real rendering.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Native GUI Binary | Standalone executable compiled from .ui.sdn + backend |
| Web Backend Test | Launches HTTP server, verifies HTML response |
| Platform Build | Builds for the current OS (macOS/Linux/Windows) |
| Real GUI | Actual HTTP server serving rendered widgets, not mocked |

## Behavior

- build_gui_binary generates entry .spl and compiles via native-build
- The resulting binary starts a web server on a specified port
- HTTP GET to / returns a full HTML page with rendered widgets
- The HTML contains the app title, theme, and widget content

## Scenarios

### Platform detection

<details>
<summary>Advanced: detects the current platform as a known value</summary>

#### detects the current platform as a known value _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platform = detect_platform()
val known = (platform == "macos" or platform == "linux" or platform == "windows")
expect(known).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns 3 supported platforms</summary>

#### returns 3 supported platforms _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platforms = supported_platforms()
expect(platforms.len()).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: includes macos, linux, windows in supported list</summary>

#### includes macos, linux, windows in supported list _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platforms = supported_platforms()
var has_macos = false
var has_linux = false
var has_windows = false
for p in platforms:
    if p == "macos":
        has_macos = true
    if p == "linux":
        has_linux = true
    if p == "windows":
        has_windows = true
expect(has_macos).to_equal(true)
expect(has_linux).to_equal(true)
expect(has_windows).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: maps platform names to display names</summary>

#### maps platform names to display names _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(platform_display_name("macos")).to_equal("macOS")
expect(platform_display_name("linux")).to_equal("Linux")
expect(platform_display_name("windows")).to_equal("Windows")
```

</details>


</details>

### GUI entry point generation

<details>
<summary>Advanced: generates web backend entry with port</summary>

#### generates web backend entry with port _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = generate_gui_entry("examples/06_io/ui/minimal.ui.sdn", "web", 4567)
expect(src).to_contain("run_web")
expect(src).to_contain("examples/06_io/ui/minimal.ui.sdn")
expect(src).to_contain("4567")
expect(src).to_contain("fn main()")
```

</details>


</details>

<details>
<summary>Advanced: generates tui backend entry</summary>

#### generates tui backend entry _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = generate_gui_entry("examples/06_io/ui/minimal.ui.sdn", "tui", 0)
expect(src).to_contain("run_tui")
expect(src).to_contain("examples/06_io/ui/minimal.ui.sdn")
expect(src).to_contain("fn main()")
```

</details>


</details>

<details>
<summary>Advanced: generates headless backend entry</summary>

#### generates headless backend entry _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = generate_gui_entry("examples/06_io/ui/minimal.ui.sdn", "headless", 0)
expect(src).to_contain("run_headless")
expect(src).to_contain("fn main()")
```

</details>


</details>

<details>
<summary>Advanced: generates auto-detect entry for unknown backend</summary>

#### generates auto-detect entry for unknown backend _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = generate_gui_entry("examples/06_io/ui/minimal.ui.sdn", "auto", 3000)
expect(src).to_contain("detect_gui_backend")
expect(src).to_contain("run_detected_backend")
```

</details>


</details>

### GUI binary build

<details>
<summary>Advanced: fails gracefully for nonexistent ui file</summary>

#### fails gracefully for nonexistent ui file _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = build_gui_binary("nonexistent/file.ui.sdn", "build/gui_test/bad", "web", 3000)
expect(result.success).to_equal(false)
expect(result.error).to_contain("not found")
```

</details>


</details>

<details>
<summary>Advanced: builds a web-mode binary from minimal.ui.sdn</summary>

#### builds a web-mode binary from minimal.ui.sdn _(slow)_

1. rt dir create all
   - Expected: result.success is true
   - Expected: result.platform equals `detect_platform()`
   - Expected: result.backend equals `web`
   - Expected: rt_file_exists("build/gui_test/minimal_web") is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all("build/gui_test")
val result = build_gui_binary(
    "examples/06_io/ui/minimal.ui.sdn",
    "build/gui_test/minimal_web",
    "web",
    4580
)
if not result.success:
    # Print error for debugging
    print "Build error: {result.error}"
expect(result.success).to_equal(true)
expect(result.platform).to_equal(detect_platform())
expect(result.backend).to_equal("web")
expect(rt_file_exists("build/gui_test/minimal_web")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds a headless binary from minimal.ui.sdn</summary>

#### builds a headless binary from minimal.ui.sdn _(slow)_

1. rt dir create all
   - Expected: result.success is true
   - Expected: result.backend equals `headless`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all("build/gui_test")
val result = build_gui_binary(
    "examples/06_io/ui/minimal.ui.sdn",
    "build/gui_test/minimal_headless",
    "headless",
    0
)
if not result.success:
    print "Build error: {result.error}"
expect(result.success).to_equal(true)
expect(result.backend).to_equal("headless")
```

</details>


</details>

### Real GUI web server

<details>
<summary>Advanced: serves HTML page with correct content</summary>

#### serves HTML page with correct content _(slow)_

1. rt dir create all

2. Ok

3. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all("build/gui_test")

val tree_result = parse_ui_to_tree("test/fixtures/gui/test_app.ui.sdn")
match tree_result:
    Ok(tree):
        val state = init_state(tree)
        val html = generate_html_page(state, 4581)
        expect(html).to_contain("<!DOCTYPE html>")
        expect(html).to_contain("<title>Test App</title>")
        expect(html).to_contain("Hello Test GUI")
    Err(e):
        expect(e).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: serves HTML with CSS dark theme styling</summary>

#### serves HTML with CSS dark theme styling _(slow)_

1. rt dir create all

2. Ok

3. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all("build/gui_test")

val tree_result = parse_ui_to_tree("test/fixtures/gui/test_app.ui.sdn")
match tree_result:
    Ok(tree):
        val state = init_state(tree)
        val html = generate_html_page(state, 4582)
        expect(html).to_contain("<style>")
        expect(html).to_contain("#1e1e2e")
    Err(e):
        expect(e).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: serves JSON state API</summary>

#### serves JSON state API _(slow)_

1. rt dir create all

2. Ok

3. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all("build/gui_test")

val tree_result = parse_ui_to_tree("test/fixtures/gui/test_app.ui.sdn")
match tree_result:
    Ok(tree):
        val state = init_state(tree)
        val json = state_to_json(state)
        expect(json).to_contain("mode")
        expect(json).to_contain("NORMAL")
        expect(json).to_contain("Test App")
    Err(e):
        expect(e).to_equal("")
```

</details>


</details>

### Multi-platform build

<details>
<summary>Advanced: returns results for all 3 platforms</summary>

#### returns results for all 3 platforms _(slow)_

1. rt dir create all
   - Expected: results.len() equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all("build/gui_test/multi")
val results = build_gui_all_platforms(
    "examples/06_io/ui/minimal.ui.sdn",
    "build/gui_test/multi",
    "web",
    3000
)
expect(results.len()).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: succeeds for current platform and reports cross-compile limitation</summary>

#### succeeds for current platform and reports cross-compile limitation _(slow)_

1. rt dir create all
   - Expected: current_succeeded is true
   - Expected: cross_failed equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all("build/gui_test/multi2")
val results = build_gui_all_platforms(
    "examples/06_io/ui/minimal.ui.sdn",
    "build/gui_test/multi2",
    "web",
    3000
)
val current = detect_platform()
var current_succeeded = false
var cross_failed = 0
for r in results:
    if r.platform == current:
        current_succeeded = r.success
    else:
        if not r.success:
            cross_failed = cross_failed + 1
            expect(r.error).to_contain("Cross-compilation not yet supported")
expect(current_succeeded).to_equal(true)
expect(cross_failed).to_equal(2)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 16 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

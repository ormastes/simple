# Native GUI Binary Build & Real GUI Test Specification

> Verifies that GUI apps can be built into standalone native binaries for the current platform and that those binaries actually serve a real GUI (web mode) with correct HTML content.

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
| Updated | 2026-08-26 |
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

- detects the current platform as a known value
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects the current platform as a known value")
val platform = detect_platform()
val known = (platform == "macos" or platform == "linux" or platform == "windows")
expect(known).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns 3 supported platforms</summary>

#### returns 3 supported platforms _(slow)_

- returns 3 supported platforms
   - Expected: platforms.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns 3 supported platforms")
val platforms = supported_platforms()
expect(platforms.len()).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: includes macos, linux, windows in supported list</summary>

#### includes macos, linux, windows in supported list _(slow)_

- includes macos, linux, windows in supported list
   - Expected: has_macos is true
   - Expected: has_linux is true
   - Expected: has_windows is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes macos, linux, windows in supported list")
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

- maps platform names to display names
   - Expected: platform_display_name("macos") equals `macOS`
   - Expected: platform_display_name("linux") equals `Linux`
   - Expected: platform_display_name("windows") equals `Windows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps platform names to display names")
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

- generates web backend entry with port


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates web backend entry with port")
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

- generates tui backend entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates tui backend entry")
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

- generates headless backend entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates headless backend entry")
val src = generate_gui_entry("examples/06_io/ui/minimal.ui.sdn", "headless", 0)
expect(src).to_contain("run_headless")
expect(src).to_contain("fn main()")
```

</details>


</details>

<details>
<summary>Advanced: generates auto-detect entry for unknown backend</summary>

#### generates auto-detect entry for unknown backend _(slow)_

- generates auto-detect entry for unknown backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates auto-detect entry for unknown backend")
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

- fails gracefully for nonexistent ui file
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails gracefully for nonexistent ui file")
val result = build_gui_binary("nonexistent/file.ui.sdn", "build/gui_test/bad", "web", 3000)
expect(result.success).to_equal(false)
expect(result.error).to_contain("not found")
```

</details>


</details>

<details>
<summary>Advanced: builds a web-mode binary from minimal.ui.sdn</summary>

#### builds a web-mode binary from minimal.ui.sdn _(slow)_

- builds a web-mode binary from minimal.ui.sdn
   - Expected: result.success is true
   - Expected: result.platform equals `detect_platform()`
   - Expected: result.backend equals `web`
   - Expected: file_exists("build/gui_test/minimal_web") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds a web-mode binary from minimal.ui.sdn")
"""
This test compiles examples/06_io/ui/minimal.ui.sdn into a native binary
with the web backend. The binary should exist after compilation.
"""
dir_create_all("build/gui_test")
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
expect(file_exists("build/gui_test/minimal_web")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds a headless binary from minimal.ui.sdn</summary>

#### builds a headless binary from minimal.ui.sdn _(slow)_

- builds a headless binary from minimal.ui.sdn
   - Expected: result.success is true
   - Expected: result.backend equals `headless`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds a headless binary from minimal.ui.sdn")
dir_create_all("build/gui_test")
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

- serves HTML page with correct content
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serves HTML page with correct content")
"""
1. Generate a web server entry point .spl
2. Launch it via the Simple interpreter as a background process
3. Wait for server to start
4. HTTP GET / and verify HTML response
5. Kill the process
"""
dir_create_all("build/gui_test")

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

- serves HTML with CSS dark theme styling
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serves HTML with CSS dark theme styling")
"""
Verify that the rendered page includes dark theme CSS.
"""
dir_create_all("build/gui_test")

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

- serves JSON state API
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serves JSON state API")
"""
Verify the /api/state endpoint returns JSON with app state.
"""
dir_create_all("build/gui_test")

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

- returns results for all 3 platforms
   - Expected: results.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns results for all 3 platforms")
dir_create_all("build/gui_test/multi")
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

- succeeds for current platform and reports cross-compile limitation
   - Expected: current_succeeded is true
   - Expected: cross_failed equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("succeeds for current platform and reports cross-compile limitation")
dir_create_all("build/gui_test/multi2")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac5e817b9ebb313732cf06099c98f84baef04c2c0ebe284f1e19072d9d3365e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac5e817b9ebb313732cf06099c98f84baef04c2c0ebe284f1e19072d9d3365e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac5e817b9ebb313732cf06099c98f84baef04c2c0ebe284f1e19072d9d3365e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gui/native_gui_build_spec.spl
mirror: doc/06_spec/03_system/gui/native_gui_build_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/native_gui_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/native_gui_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/native_gui_build_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/native_gui_build_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the current platform as a known value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/native_gui_build_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 3 supported platforms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/native_gui_build_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes macos, linux, windows in supported list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

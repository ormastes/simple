# Simulate after state (button rendered)

> capture_before_ffi(before_buffer)

<!-- sdn-diagram:id=screenshot_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=screenshot_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

screenshot_ffi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=screenshot_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simulate after state (button rendered)

capture_before_ffi(before_buffer)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

capture_before_ffi(before_buffer)

            val after_buffer = """
            +------------------+
            |   [ Click Me ]   |
            |                  |
            |   Status: OK     |
            +------------------+

## Scenarios

### Screenshot FFI

#### Control Functions

#### enables and disables screenshot capture

1. disable ffi screenshots
2. expect is ffi screenshots enabled
3. enable ffi screenshots
4. expect is ffi screenshots enabled
5. disable ffi screenshots
6. expect is ffi screenshots enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
disable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == false

enable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == true

disable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == false
```

</details>

#### sets refresh mode

1. set ffi refresh
2. set ffi refresh


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_ffi_refresh(true)
set_ffi_refresh(false)
# No assertion needed - just verifies FFI calls work
```

</details>

#### Output Directory

#### sets output directory

1. set ffi output dir
2. set ffi output dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_ffi_output_dir("doc/spec/test_images")
# No assertion needed - just verifies FFI calls work
# Reset to default
set_ffi_output_dir("doc/06_spec/image")
```

</details>

#### Test Context

#### sets and clears test context

1. set ffi test context
2. clear ffi test context


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_ffi_test_context("test/unit/ui/button_spec.spl", "renders button")
clear_ffi_test_context()
# No assertion needed - just verifies FFI calls work
```

</details>

#### generates correct paths from context

1. enable ffi screenshots
2. set ffi output dir
3. set ffi test context
4. expect before path contains
5. expect before path contains
6. expect after path contains
7. clear ffi test context
8. disable ffi screenshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_ffi_screenshots()
set_ffi_output_dir("doc/06_spec/image")
set_ffi_test_context("test/unit/ui/button_spec.spl", "renders button")

val before_path = get_screenshot_path_ffi(CAPTURE_TYPE_BEFORE)
val after_path = get_screenshot_path_ffi(CAPTURE_TYPE_AFTER)

# Paths should contain the test name
expect before_path.contains("renders_button") == true
expect before_path.contains("before") == true
expect after_path.contains("after") == true

clear_ffi_test_context()
disable_ffi_screenshots()
```

</details>

#### Terminal Buffer Capture

#### captures before terminal buffer

1. enable ffi screenshots
2. set ffi test context
3. clear ffi captures
4. clear ffi test context
5. disable ffi screenshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_ffi_screenshots()
set_ffi_test_context("test/unit/ui/text_spec.spl", "displays text")

val buffer = "Hello, World!\nThis is a test."
val result = capture_before_ffi(buffer)

# May be false if directory doesn't exist, but FFI call should succeed
clear_ffi_captures()
clear_ffi_test_context()
disable_ffi_screenshots()
```

</details>

#### captures after terminal buffer

1. enable ffi screenshots
2. set ffi test context
3. clear ffi captures
4. clear ffi test context
5. disable ffi screenshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_ffi_screenshots()
set_ffi_test_context("test/unit/ui/text_spec.spl", "displays text")

val buffer = "After state\nWith changes."
val result = capture_after_ffi(buffer)

clear_ffi_captures()
clear_ffi_test_context()
disable_ffi_screenshots()
```

</details>

#### ANSI Buffer Capture

#### captures ANSI formatted terminal output

1. enable ffi screenshots
2. set ffi test context
3. clear ffi captures
4. clear ffi test context
5. disable ffi screenshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_ffi_screenshots()
set_ffi_test_context("test/unit/ui/ansi_spec.spl", "renders colored text")

# ANSI escape sequences for colored output (simplified for testing)
val ansi_buffer = "Red Text\nGreen Text\nBlue Text"
val result = capture_before_ffi(ansi_buffer)

clear_ffi_captures()
clear_ffi_test_context()
disable_ffi_screenshots()
```

</details>

#### Query Functions

#### checks if screenshot exists

1. enable ffi screenshots
2. set ffi test context
3. clear ffi test context
4. disable ffi screenshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_ffi_screenshots()
set_ffi_test_context("test/nonexistent/spec.spl", "nonexistent test")

# Should return false for non-existent screenshot
val exists = screenshot_exists_ffi(CAPTURE_TYPE_BEFORE)
expect exists == false

clear_ffi_test_context()
disable_ffi_screenshots()
```

</details>

#### Real-World Example

#### captures TUI widget rendering

1. enable ffi screenshots
2. set ffi output dir
3. set ffi test context
4. capture before ffi
5. capture after ffi
6. clear ffi captures
7. clear ffi test context
8. disable ffi screenshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_ffi_screenshots()
set_ffi_output_dir("doc/06_spec/image")
set_ffi_test_context("test/unit/ui/tui/button_spec.spl", "renders button with border")

# Simulate before state (empty)
val before_buffer = """
+------------------+
|                  |
|                  |
|                  |
+------------------+
"""
capture_before_ffi(before_buffer)

# Simulate after state (button rendered)
val after_buffer = """
+------------------+
|   [ Click Me ]   |
|                  |
|   Status: OK     |
+------------------+
"""
capture_after_ffi(after_buffer)

clear_ffi_captures()
clear_ffi_test_context()
disable_ffi_screenshots()
```

</details>

#### captures multiple screenshots in sequence

1. enable ffi screenshots
2. set ffi output dir
3. set ffi test context
4. capture before ffi
5. capture after ffi
6. clear ffi captures
7. clear ffi test context
8. set ffi test context
9. capture before ffi
10. capture after ffi
11. clear ffi captures
12. clear ffi test context
13. disable ffi screenshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_ffi_screenshots()
set_ffi_output_dir("doc/06_spec/image")

# First test
set_ffi_test_context("test/unit/ui/list_spec.spl", "empty list")
capture_before_ffi("[]")
capture_after_ffi("[]")
clear_ffi_captures()
clear_ffi_test_context()

# Second test
set_ffi_test_context("test/unit/ui/list_spec.spl", "list with items")
capture_before_ffi("[]")
capture_after_ffi("[1, 2, 3]")
clear_ffi_captures()
clear_ffi_test_context()

disable_ffi_screenshots()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

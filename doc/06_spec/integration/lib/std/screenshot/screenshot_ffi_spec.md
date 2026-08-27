# Simulate after state (button rendered)

> capture_before_ffi(before_buffer)

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
| Source | `test/integration/lib/std/screenshot/screenshot_ffi_spec.spl` |
| Updated | 2026-08-26 |
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

- enables and disables screenshot capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("enables and disables screenshot capture")
disable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == false

enable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == true

disable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == false
```

</details>

#### sets refresh mode

- sets refresh mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets refresh mode")
set_ffi_refresh(true)
set_ffi_refresh(false)
# No assertion needed - just verifies FFI calls work
```

</details>

#### Output Directory

#### sets output directory

- sets output directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets output directory")
set_ffi_output_dir("doc/spec/test_images")
# No assertion needed - just verifies FFI calls work
# Reset to default
set_ffi_output_dir("doc/06_spec/image")
```

</details>

#### Test Context

#### sets and clears test context

- sets and clears test context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets and clears test context")
set_ffi_test_context("test/unit/ui/button_spec.spl", "renders button")
clear_ffi_test_context()
# No assertion needed - just verifies FFI calls work
```

</details>

#### generates correct paths from context

- generates correct paths from context


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates correct paths from context")
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

- captures before terminal buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("captures before terminal buffer")
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

- captures after terminal buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("captures after terminal buffer")
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

- captures ANSI formatted terminal output


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("captures ANSI formatted terminal output")
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

- checks if screenshot exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("checks if screenshot exists")
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

- captures TUI widget rendering


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("captures TUI widget rendering")
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

- captures multiple screenshots in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("captures multiple screenshots in sequence")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bf2cac9d983cfc42f30b333de1fd2028baf9739bd51b7d3b40b549edcb702a89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf2cac9d983cfc42f30b333de1fd2028baf9739bd51b7d3b40b549edcb702a89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf2cac9d983cfc42f30b333de1fd2028baf9739bd51b7d3b40b549edcb702a89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/lib/std/screenshot/screenshot_ffi_spec.spl
mirror: doc/06_spec/integration/lib/std/screenshot/screenshot_ffi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/std/screenshot/screenshot_ffi_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/integration/lib/std/screenshot/screenshot_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/std/screenshot/screenshot_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/std/screenshot/screenshot_ffi_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables and disables screenshot capture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/screenshot/screenshot_ffi_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets refresh mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/screenshot/screenshot_ffi_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets output directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

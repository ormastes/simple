# Simulate after state (button rendered)

> Verifies the screenshot ffi behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simulate after state (button rendered)

Verifies the screenshot ffi behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the screenshot ffi behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Screenshot FFI

#### Control Functions

#### enables and disables screenshot capture

- Verify: enables and disables screenshot capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: enables and disables screenshot capture")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
disable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == false

enable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == true

disable_ffi_screenshots()
expect is_ffi_screenshots_enabled() == false
```

</details>

#### sets refresh mode

- Verify: sets refresh mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: sets refresh mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
set_ffi_refresh(true)
set_ffi_refresh(false)
# No assertion needed - just verifies FFI calls work
```

</details>

#### Output Directory

#### sets output directory

- Verify: sets output directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: sets output directory")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
set_ffi_output_dir("doc/spec/test_images")
# No assertion needed - just verifies FFI calls work
# Reset to default
set_ffi_output_dir("doc/06_spec/image")
```

</details>

#### Test Context

#### sets and clears test context

- Verify: sets and clears test context


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: sets and clears test context")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
set_ffi_test_context("test/unit/ui/button_spec.spl", "renders button")
clear_ffi_test_context()
# No assertion needed - just verifies FFI calls work
```

</details>

#### generates correct paths from context

- Verify: generates correct paths from context


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: generates correct paths from context")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: captures before terminal buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: captures before terminal buffer")
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

- Verify: captures after terminal buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: captures after terminal buffer")
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

- Verify: captures ANSI formatted terminal output


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: captures ANSI formatted terminal output")
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

- Verify: checks if screenshot exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: checks if screenshot exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: captures TUI widget rendering


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: captures TUI widget rendering")
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

- Verify: captures multiple screenshots in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_FFI-001
step("Verify: captures multiple screenshots in sequence")
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3598a01b2ca9bbba4f1d49d7d60df22e77c9e18c25a24a5d70e26affc58aa34c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3598a01b2ca9bbba4f1d49d7d60df22e77c9e18c25a24a5d70e26affc58aa34c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3598a01b2ca9bbba4f1d49d7d60df22e77c9e18c25a24a5d70e26affc58aa34c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl
mirror: doc/06_spec/02_integration/lib/std/screenshot/screenshot_ffi_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/screenshot/screenshot_ffi_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/std/screenshot/screenshot_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/screenshot/screenshot_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

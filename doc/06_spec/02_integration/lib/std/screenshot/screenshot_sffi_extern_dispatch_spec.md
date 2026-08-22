# screenshot_sffi_extern_dispatch_spec

> Verifies the screenshot sffi extern dispatch behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# screenshot_sffi_extern_dispatch_spec

Verifies the screenshot sffi extern dispatch behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the screenshot sffi extern dispatch behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Screenshot SFFI extern dispatch

#### every wrapped rt_screenshot_* extern dispatches

#### dispatches the enable/disable/query externs

- Verify: dispatches the enable/disable/query externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_SFFI_E-001
step("Verify: dispatches the enable/disable/query externs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
enable_sffi_screenshots()
expect is_sffi_screenshots_enabled() == true
disable_sffi_screenshots()
expect is_sffi_screenshots_enabled() == false
```

</details>

#### dispatches the refresh extern

- Verify: dispatches the refresh extern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_SFFI_E-001
step("Verify: dispatches the refresh extern")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
set_sffi_refresh(true)
set_sffi_refresh(false)
expect is_sffi_screenshots_enabled() == false
```

</details>

#### dispatches the output-dir and context externs

- Verify: dispatches the output-dir and context externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_SFFI_E-001
step("Verify: dispatches the output-dir and context externs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
set_sffi_output_dir("build/screenshot_sffi_dispatch")
set_sffi_test_context("test/dispatch/spec.spl", "dispatch case")
val path = get_screenshot_path_sffi(CAPTURE_TYPE_BEFORE)
expect path.contains("dispatch") == true
clear_sffi_test_context()
```

</details>

#### dispatches the capture and clear externs

- Verify: dispatches the capture and clear externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_SFFI_E-001
step("Verify: dispatches the capture and clear externs")
enable_sffi_screenshots()
set_sffi_refresh(true)
set_sffi_output_dir("build/screenshot_sffi_dispatch")
set_sffi_test_context("test/dispatch/spec.spl", "capture case")
expect capture_before_sffi("before-buffer") == true
expect capture_after_sffi("after-buffer") == true
clear_sffi_captures()
clear_sffi_test_context()
disable_sffi_screenshots()
```

</details>

#### dispatches the exists extern for a missing capture

- Verify: dispatches the exists extern for a missing capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SCREENSHOT_SCREENSHOT_SFFI_E-001
step("Verify: dispatches the exists extern for a missing capture")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
set_sffi_test_context("test/dispatch/never_captured.spl", "absent case")
val found = screenshot_exists_ffi(CAPTURE_TYPE_AFTER)
expect found == false
clear_sffi_test_context()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `49189079af4411decc0180252ebb3bcc8b7948a954960f223f026baea928888c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49189079af4411decc0180252ebb3bcc8b7948a954960f223f026baea928888c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49189079af4411decc0180252ebb3bcc8b7948a954960f223f026baea928888c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.spl
mirror: doc/06_spec/02_integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

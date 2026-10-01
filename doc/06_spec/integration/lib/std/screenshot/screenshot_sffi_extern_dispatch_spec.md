# Screenshot Sffi Extern Dispatch Specification

> Tests covering Screenshot SFFI extern dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Screenshot Sffi Extern Dispatch Specification

## Scenarios

### Screenshot SFFI extern dispatch

#### every wrapped rt_screenshot_* extern dispatches

#### dispatches the enable/disable/query externs

- dispatches the enable/disable/query externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatches the enable/disable/query externs")
enable_sffi_screenshots()
expect is_sffi_screenshots_enabled() == true
disable_sffi_screenshots()
expect is_sffi_screenshots_enabled() == false
```

</details>

#### dispatches the refresh extern

- dispatches the refresh extern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatches the refresh extern")
set_sffi_refresh(true)
set_sffi_refresh(false)
expect is_sffi_screenshots_enabled() == false
```

</details>

#### dispatches the output-dir and context externs

- dispatches the output-dir and context externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatches the output-dir and context externs")
set_sffi_output_dir("build/screenshot_sffi_dispatch")
set_sffi_test_context("test/dispatch/spec.spl", "dispatch case")
val path = get_screenshot_path_sffi(CAPTURE_TYPE_BEFORE)
expect path.contains("dispatch") == true
clear_sffi_test_context()
```

</details>

#### dispatches the capture and clear externs

- dispatches the capture and clear externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatches the capture and clear externs")
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

- dispatches the exists extern for a missing capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatches the exists extern for a missing capture")
set_sffi_test_context("test/dispatch/never_captured.spl", "absent case")
val found = screenshot_exists_ffi(CAPTURE_TYPE_AFTER)
expect found == false
clear_sffi_test_context()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Screenshot SFFI extern dispatch.
- Screenshot SFFI extern dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `cf492277579d032dbd57afe4f6e1869478d8559a02fc62c6862ae08b6ca4e5a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf492277579d032dbd57afe4f6e1869478d8559a02fc62c6862ae08b6ca4e5a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf492277579d032dbd57afe4f6e1869478d8559a02fc62c6862ae08b6ca4e5a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.spl
mirror: doc/06_spec/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=65 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches the enable/disable/query externs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/screenshot/screenshot_sffi_extern_dispatch_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches the refresh extern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

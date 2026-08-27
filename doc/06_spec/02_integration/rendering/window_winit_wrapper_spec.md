# Window Winit Wrapper Specification

> Tests covering window_winit safety guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Winit Wrapper Specification

## Scenarios

### window_winit safety guards

#### invalid event loop

#### yields an invalid window without touching the runtime

- yields an invalid window without touching the runtime
   - Expected: win.is_valid is false
   - Expected: win.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("yields an invalid window without touching the runtime")
# An invalid loop must NOT call rt_winit_window_new (which is absent
# from the test binary) — the guard returns an invalid window first.
val lp = WinitLoop(handle: 0, is_valid: false)
val win = winit_window_new(lp, 96, 72, "guard")
expect(win.is_valid).to_equal(false)
expect(win.handle).to_equal(0)
```

</details>

<details>
<summary>Advanced: reports absent polling without entering the drain loop</summary>

#### reports absent polling without entering the drain loop

- reports absent polling without entering the drain loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports absent polling without entering the drain loop")
# The early-out (`if not lp.is_valid: return nil`) means no event is
# ever polled, so there is no event to leak — and no extern is called.
val lp = WinitLoop(handle: 0, is_valid: false)
expect(winit_poll_close_requested(lp)).to_be_nil()
```

</details>


</details>

#### invalid window

#### present fails closed (guard prevents the extern call)

- present fails closed (guard prevents the extern call)
   - Expected: winit_present_rgba(win, 2, 2, pixels) is false
   - Expected: win.is_valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("present fails closed (guard prevents the extern call)")
val win = WinitWindow(handle: 0, is_valid: false)
val pixels: [i64] = [0, 0, 0, 0]
expect(winit_present_rgba(win, 2, 2, pixels)).to_equal(false)
# Reaching here without a missing-extern abort proves the guard held.
expect(win.is_valid).to_equal(false)
```

</details>

#### free on invalid handles

<details>
<summary>Advanced: loop and window free are no-ops on invalid handles</summary>

#### loop and window free are no-ops on invalid handles

- loop and window free are no-ops on invalid handles
   - Expected: lp.is_valid is false
   - Expected: win.is_valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("loop and window free are no-ops on invalid handles")
val lp = WinitLoop(handle: 0, is_valid: false)
val win = WinitWindow(handle: 0, is_valid: false)
winit_loop_free(lp)
winit_window_free(win)
expect(lp.is_valid).to_equal(false)
expect(win.is_valid).to_equal(false)
```

</details>


</details>

#### native event ABI

#### uses the scalar accessors exported by the winit provider

- uses the scalar accessors exported by the winit provider
   - Expected: source does not contain `rt_winit_event_keyboard_input`
   - Expected: source does not contain `rt_winit_window_present_rgba(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the scalar accessors exported by the winit provider")
val source = file_read("src/lib/nogc_sync_mut/io/window_winit.spl")
expect(source).to_contain("rt_winit_event_key_pressed")
expect(source).to_contain("rt_winit_event_mouse_pressed")
expect(source).to_contain("rt_winit_event_mouse_x_milli")
expect(source).to_contain("rt_winit_event_wheel_y_milli")
expect(source.contains("rt_winit_event_keyboard_input")).to_equal(false)
expect(source).to_contain("rt_winit_window_staging_ptr")
expect(source).to_contain("rt_write_u32s_to_raw")
expect(source).to_contain("rt_winit_window_present_staged")
expect(source.contains("rt_winit_window_present_rgba(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/window_winit_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering window_winit safety guards.
- window_winit safety guards

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

- Canonical SPipe generation for source `66bf0afdaf46d487f114e8c0f78ea020f75c1d5d8f9c9cb886d3f50e21e84123`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66bf0afdaf46d487f114e8c0f78ea020f75c1d5d8f9c9cb886d3f50e21e84123`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66bf0afdaf46d487f114e8c0f78ea020f75c1d5d8f9c9cb886d3f50e21e84123`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/rendering/window_winit_wrapper_spec.spl
mirror: doc/06_spec/02_integration/rendering/window_winit_wrapper_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/02_integration/rendering/window_winit_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/window_winit_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/window_winit_wrapper_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/02_integration/rendering/window_winit_wrapper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/window_winit_wrapper_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yields an invalid window without touching the runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/window_winit_wrapper_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports absent polling without entering the drain loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/window_winit_wrapper_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'present fails closed (guard prevents the extern call)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# requestAnimationFrame Boundary Alignment

> BrowserSession and the canonical JavaScript timer owner align staggered requestAnimationFrame registrations to one document-clock refresh boundary. Callbacks registered during dispatch wait for the following boundary, canceled handles stay inert, and both observable frames lower through Draw IR and Engine2D without a private clock or painter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# requestAnimationFrame Boundary Alignment

BrowserSession and the canonical JavaScript timer owner align staggered requestAnimationFrame registrations to one document-clock refresh boundary. Callbacks registered during dispatch wait for the following boundary, canceled handles stay inert, and both observable frames lower through Draw IR and Engine2D without a private clock or painter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BrowserSession and the canonical JavaScript timer owner align staggered
requestAnimationFrame registrations to one document-clock refresh boundary.
Callbacks registered during dispatch wait for the following boundary, canceled
handles stay inert, and both observable frames lower through Draw IR and
Engine2D without a private clock or painter.

## Scenarios

### requestAnimationFrame boundary alignment

#### should keep timer and animation-frame cancellation domains separate

- should keep timer and animation-frame cancellation domains separate
   - Artifact capture: after_step
- Register the browser callback
   - Artifact capture: after_step
- Advance the monotonic browser clock
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.advance_time(15) equals `0`
- Dispatch events and animation frames
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.advance_time(16) equals `2`
- Observe updated canonical Draw IR pixels and released resources
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep timer and animation-frame cancellation domains separate")
step("Register the browser callback")
var session = setup_cancel_domain_fixture()
check_cancel_domain_registration(session)
check_node_cancel_domain_handle_metadata()

    step("Observe updated canonical Draw IR pixels and released resources")
    check_cancel_domain_pixels_and_resources(session)

step("Dispatch events and animation frames")
val _ = session.dispatch_dom_event(
    "stage", "click", true, true
)
val _ = session.dispatch_dom_event(
    "stage", "click", true, true
)
expect(session.advance_time(16)).to_equal(2)
expect(_read_js_text(
    session,
    "callbackLog+':'+clickCount+':'+frameStamp"
)).to_equal("FT:1:16")

    step("Advance to the shared frame boundary")
    expect(session.advance_time(16)).to_equal(2)

    step("Schedule a callback during dispatch")
    check_nested_callback_deferred(session)

    step("Render two aligned animation frames")
    check_aligned_draw_ir_frames(session)

it "should preserve aligned deadlines across clock edge cases":
    step("Align a skipped refresh from a nonzero document origin")
    check_nonzero_origin_skipped_boundary()

    step("Keep an overflowed nested frame out of the current drain")
    check_overflow_safe_nested_frame()

    step("Refresh Node-compatible animation handles exactly")
    check_node_compatible_raf_refresh_metadata()

    step("Saturate worker wakeup after the drain cap")
    check_worker_wakeup_saturates_after_drain_cap()
```

</details>

#### should align staggered and nested callbacks to deterministic frames

- should align staggered and nested callbacks to deterministic frames
   - Artifact capture: after_step
- Schedule staggered callbacks before one refresh
   - Artifact capture: after_step
- Advance to the shared frame boundary
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.advance_time(16) equals `2`
- Schedule a callback during dispatch
   - Artifact capture: after_step
- Render two aligned animation frames
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should align staggered and nested callbacks to deterministic frames")
step("Schedule staggered callbacks before one refresh")
var session = setup_raf_alignment_fixture()
check_shared_frame_deadline(session)

step("Advance to the shared frame boundary")
expect(session.advance_time(16)).to_equal(2)

step("Schedule a callback during dispatch")
check_nested_callback_deferred(session)

step("Render two aligned animation frames")
check_aligned_draw_ir_frames(session)
```

</details>

#### should preserve aligned deadlines across clock edge cases

- should preserve aligned deadlines across clock edge cases
   - Text capture: after_step
- Align a skipped refresh from a nonzero document origin
   - Text capture: after_step
- Keep an overflowed nested frame out of the current drain
   - Text capture: after_step
- Refresh Node-compatible animation handles exactly
   - Text capture: after_step
- Saturate worker wakeup after the drain cap
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve aligned deadlines across clock edge cases")
step("Align a skipped refresh from a nonzero document origin")
check_nonzero_origin_skipped_boundary()

step("Keep an overflowed nested frame out of the current drain")
check_overflow_safe_nested_frame()

step("Refresh Node-compatible animation handles exactly")
check_node_compatible_raf_refresh_metadata()

step("Saturate worker wakeup after the drain cap")
check_worker_wakeup_saturates_after_drain_cap()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b3efcc4a31a4c45848bfbc46933aafce030fbb6bb572377a23567bd6bba24bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b3efcc4a31a4c45848bfbc46933aafce030fbb6bb572377a23567bd6bba24bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b3efcc4a31a4c45848bfbc46933aafce030fbb6bb572377a23567bd6bba24bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/request_animation_frame_alignment_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/request_animation_frame_alignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/request_animation_frame_alignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:542:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep timer and animation-frame cancellation domains separate' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:542:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep timer and animation-frame cancellation domains separate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:577:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should align staggered and nested callbacks to deterministic frames' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:577:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should align staggered and nested callbacks to deterministic frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:596:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve aligned deadlines across clock edge cases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:596:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve aligned deadlines across clock edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

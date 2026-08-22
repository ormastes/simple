# requestAnimationFrame Boundary Alignment

> Verifies the request animation frame alignment behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# requestAnimationFrame Boundary Alignment

Verifies the request animation frame alignment behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the request animation frame alignment behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### requestAnimationFrame boundary alignment

#### should keep timer and animation-frame cancellation domains separate

- Verify: should keep timer and animation-frame cancellation domains separate
   - Artifact capture: after_step
- Register the browser callback
   - Artifact capture: after_step
- Advance the monotonic browser clock
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.advance_time(15) equals `0)  # oracle: pinned constant asserted by this scenario`
- Dispatch events and animation frames
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.advance_time(16) equals `2)  # oracle: pinned constant asserted by this scenario`
- Observe updated canonical Draw IR pixels and released resources
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: should keep timer and animation-frame cancellation domains separate")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Register the browser callback")
var session = setup_cancel_domain_fixture()
check_cancel_domain_registration(session)
check_node_cancel_domain_handle_metadata()

step("Advance the monotonic browser clock")
expect(session.advance_time(15)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(_read_js_text(
    session,
    "callbackLog+':'+clickCount+':'+frameStamp"
)).to_equal(":0:-1")

step("Dispatch events and animation frames")
val _ = session.dispatch_dom_event(
    "stage", "click", true, true
)
val _ = session.dispatch_dom_event(
    "stage", "click", true, true
)
expect(session.advance_time(16)).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(_read_js_text(
    session,
    "callbackLog+':'+clickCount+':'+frameStamp"
)).to_equal("FT:1:16")

step("Observe updated canonical Draw IR pixels and released resources")
check_cancel_domain_pixels_and_resources(session)
```

</details>

#### should align staggered and nested callbacks to deterministic frames

- Verify: should align staggered and nested callbacks to deterministic frames
   - Artifact capture: after_step
- Schedule staggered callbacks before one refresh
   - Artifact capture: after_step
- Advance to the shared frame boundary
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.advance_time(16) equals `2)  # oracle: pinned constant asserted by this scenario`
- Schedule a callback during dispatch
   - Artifact capture: after_step
- Render two aligned animation frames
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-004
step("Verify: should align staggered and nested callbacks to deterministic frames")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Schedule staggered callbacks before one refresh")
var session = setup_raf_alignment_fixture()
check_shared_frame_deadline(session)

step("Advance to the shared frame boundary")
expect(session.advance_time(16)).to_equal(2)  # oracle: pinned constant asserted by this scenario

step("Schedule a callback during dispatch")
check_nested_callback_deferred(session)

step("Render two aligned animation frames")
check_aligned_draw_ir_frames(session)
```

</details>

#### should preserve aligned deadlines across clock edge cases

- Verify: should preserve aligned deadlines across clock edge cases
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-006 REQ-WEB-BROWSER-017 REQ-WEB-BROWSER-021
step("Verify: should preserve aligned deadlines across clock edge cases")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f147d9aa86c49466313937578ca32e64651cd40c10323cbc2adba925befa4da0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f147d9aa86c49466313937578ca32e64651cd40c10323cbc2adba925befa4da0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f147d9aa86c49466313937578ca32e64651cd40c10323cbc2adba925befa4da0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/request_animation_frame_alignment_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/request_animation_frame_alignment_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/request_animation_frame_alignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/request_animation_frame_alignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:552:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep timer and animation-frame cancellation domains separate' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:587:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should align staggered and nested callbacks to deterministic frames' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl:607:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve aligned deadlines across clock edge cases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

# Equal innerHTML CSS Animation Restart

> An explicit body `innerHTML` replacement creates fresh descendant elements even when the replacement bytes equal the current body markup. Their CSS animations restart at the replacement epoch. Ordinary class and style mutations preserve that epoch, and the resulting frame still lowers through canonical Draw IR.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Equal innerHTML CSS Animation Restart

An explicit body `innerHTML` replacement creates fresh descendant elements even when the replacement bytes equal the current body markup. Their CSS animations restart at the replacement epoch. Ordinary class and style mutations preserve that epoch, and the resulting frame still lowers through canonical Draw IR.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

An explicit body `innerHTML` replacement creates fresh descendant elements even
when the replacement bytes equal the current body markup. Their CSS animations
restart at the replacement epoch. Ordinary class and style mutations preserve
that epoch, and the resulting frame still lowers through canonical Draw IR.

## Scenarios

### equal innerHTML CSS animation restart

#### should restart fresh descendants without restarting style mutations

- should restart fresh descendants without restarting style mutations
   - Artifact capture: after_step
- Register the browser callback
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: initial.command.color equals `0xFFEF4444u32`
   - Expected: session.css_animation_instances.len() equals `1`
   - Expected: session.css_animation_instances[0].start_time_ms equals `0`
   - Expected: state.runtime.interpreter.pending_timer_tasks.len() equals `1`
- Advance the monotonic browser clock
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: session.advance_time(100) equals `1`
   - Expected: session.css_animation_reconcile_pending is true
   - Expected: session.css_animation_instances[0].start_time_ms equals `0`
- Dispatch events and animation frames
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: session.css_animation_instances.len() equals `1`
   - Expected: session.css_animation_instances[0].start_time_ms equals `100`
   - Expected: restarted.command.color equals `0xFFEF4444u32`
- Observe updated canonical Draw IR pixels and released resources
   - Artifact capture: after_step
   - Evidence: artifact verified by 12 expected checks
   - Expected: session.css_animation_instances.len() equals `1`
   - Expected: session.css_animation_instances[0].start_time_ms equals `100`
   - Expected: styled.source_kind equals `html_ast`
   - Expected: styled.command.component_id equals `stage`
   - Expected: styled.command.x equals `0`
   - Expected: styled.command.y equals `0`
   - Expected: styled.command.width equals `8`
   - Expected: styled.command.height equals `16`
   - Expected: styled.command.color equals `0xFFEF4444u32`
   - Expected: styled.skipped_commands equals `0`
   - Expected: session.css_animation_instances.len() equals `0`
   - Expected: session.current_body_html equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 94 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should restart fresh descendants without restarting style mutations")
step("Register the browser callback")
var session = _open_equal_replacement_fixture()
val initial = _render_equal_replacement_frame(session)
expect(initial.command.color).to_equal(0xFFEF4444u32)
expect(session.css_animation_instances.len()).to_equal(1)
expect(session.css_animation_instances[0].start_time_ms).to_equal(0)
var initial_bridge_generation: i64 = -1
if val Some(state) = session.runtime_state:
    initial_bridge_generation = (
        state.runtime.interpreter.host_dom_bridge_generation
    )
else:
    fail("Expected an active browser JavaScript runtime")
expect(session.eval_script(
    "var savedMarkup=document.body.innerHTML;" +
    "var callbackLog='';" +
    "requestAnimationFrame(function(frameTime){" +
    "callbackLog='F:'+frameTime;" +
    "document.body.innerHTML=savedMarkup;" +
    "var fresh=document.getElementById('stage');" +
    "fresh.addEventListener('click',function(){" +
    "callbackLog=callbackLog+':C';" +
    "fresh.style.width='8px';},{once:true});});"
).is_ok()).to_equal(true)
if val Some(state) = session.runtime_state:
    expect(state.runtime.interpreter.pending_timer_tasks.len()).to_equal(1)
else:
    fail("Expected the animation-frame callback to be document-owned")

step("Advance the monotonic browser clock")
expect(session.advance_time(100)).to_equal(1)
expect(_read_equal_replacement_text(
    session, "callbackLog"
)).to_equal("F:100")
expect(session.css_animation_reconcile_pending).to_equal(true)
expect(session.css_animation_instances[0].start_time_ms).to_equal(0)
var replacement_bridge_generation: i64 = -1
var replacement_mutation_generation: i64 = -1
if val Some(state) = session.runtime_state:
    replacement_bridge_generation = (
        state.runtime.interpreter.host_dom_bridge_generation
    )
    replacement_mutation_generation = (
        state.runtime.interpreter.host_dom_mutation_generation
    )
    expect(replacement_bridge_generation).to_be_greater_than(
        initial_bridge_generation
    )
    expect(state.dom_bridge_generation).to_equal(
        replacement_bridge_generation
    )
else:
    fail("Expected the replaced browser DOM bridge")

step("Dispatch events and animation frames")
val restarted = _render_equal_replacement_frame(session)
expect(session.css_animation_instances.len()).to_equal(1)
expect(session.css_animation_instances[0].start_time_ms).to_equal(100)
expect(restarted.command.color).to_equal(0xFFEF4444u32)
val _ = session.dispatch_dom_event("stage", "click", true, true)
expect(_read_equal_replacement_text(
    session, "callbackLog"
)).to_equal("F:100:C")
if val Some(state) = session.runtime_state:
    expect(
        state.runtime.interpreter.host_dom_bridge_generation
    ).to_equal(replacement_bridge_generation)
    expect(
        state.runtime.interpreter.host_dom_mutation_generation
    ).to_be_greater_than(replacement_mutation_generation)
else:
    fail("Expected style mutation generation evidence")

step("Observe updated canonical Draw IR pixels and released resources")
val styled = _render_equal_replacement_frame(session)
expect(session.css_animation_instances.len()).to_equal(1)
expect(session.css_animation_instances[0].start_time_ms).to_equal(100)
expect(styled.source_kind).to_equal("html_ast")
expect(styled.command.component_id).to_equal("stage")
expect(styled.command.x).to_equal(0)
expect(styled.command.y).to_equal(0)
expect(styled.command.width).to_equal(8)
expect(styled.command.height).to_equal(16)
expect(styled.command.color).to_equal(0xFFEF4444u32)
expect(styled.rendered_commands).to_be_greater_than(0)
expect(styled.skipped_commands).to_equal(0)
_expect_exact_equal_replacement_buffer(styled)
_expect_released_equal_replacement_callbacks(session)
session.close()
expect(session.runtime_state).to_be_nil()
expect(session.css_animation_instances.len()).to_equal(0)
expect(session.current_body_html).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`
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

- Canonical SPipe generation for source `e4843b6021c74f4d117dc6dccf1131fb44fb45f9e3983a0282ba9d63b59f45ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4843b6021c74f4d117dc6dccf1131fb44fb45f9e3983a0282ba9d63b59f45ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4843b6021c74f4d117dc6dccf1131fb44fb45f9e3983a0282ba9d63b59f45ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.spl:162:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restart fresh descendants without restarting style mutations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should restart fresh descendants without restarting style mutations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Browser live default-action validation

> Click listeners may change the activation target before default behavior runs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser live default-action validation

Click listeners may change the activation target before default behavior runs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_live_default_action_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Click listeners may change the activation target before default behavior runs.
The original checkbox/radio pre-activation is rolled back when its action no
longer matches, and only the action derived from the live routed node executes.
New browsing-context targets remain distinct from current-document navigation
and fail closed when popup authority or a popup host is unavailable.

## Scenarios

### BrowserSession live default actions

#### should route only the action derived from the live target

- should route only the action derived from the live target
   - HTML capture: after_step
- Install guarded link and submit controls
   - HTML capture: after_step
- Mutate activation state inside click listeners
   - HTML capture: after_step
- Suppress stale navigation and form submission
   - HTML capture: after_step
- Preserve unchanged control activation
   - HTML capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route only the action derived from the live target")
step("Install guarded link and submit controls")
val fixture = setup_post_dispatch_activation_fixture()

step("Mutate activation state inside click listeners")
trigger_pointer_and_keyboard_mutation(fixture)

step("Suppress stale navigation and form submission")
check_invalidated_default_actions(fixture)

step("Preserve unchanged control activation")
check_live_default_action_control_case()
```

</details>

#### should never coerce a new target into the current document

- should never coerce a new target into the current document
   - HTML capture: after_step
- Install whitespace, mixed-case, named, and keyword targets
   - HTML capture: after_step
- Preserve raw new-context names and classify exact keywords
   - HTML capture: after_step
- Activate whitespace and keyword targets by pointer and Enter
   - HTML capture: after_step
- Fail popup attempts closed and preserve current-target behavior
   - HTML capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 107 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should never coerce a new target into the current document")
step("Install whitespace, mixed-case, named, and keyword targets")
val spaced_self = setup_target_context_fixture(
    " _self ", "Spaced self", false
)
val mixed_blank = setup_target_context_fixture(
    "_BLANK", "Mixed blank", false
)
val exact_blank = setup_target_context_fixture(
    "_blank", "Exact blank", false
)
val named = setup_target_context_fixture(
    "report: frame", "Named target", true
)
val mixed_self = setup_target_context_fixture(
    "_SELF", "Mixed self", false
)
val exact_self = setup_target_context_fixture(
    "_self", "Exact self", false
)
val parent_target = setup_target_context_fixture(
    "_parent", "Parent target", false
)
val top_target = setup_target_context_fixture(
    "_top", "Top target", false
)
val empty_target = setup_target_context_fixture(
    "", "Empty target", false
)

step("Preserve raw new-context names and classify exact keywords")
expect(_live_default_action(
    spaced_self, "target-link", "click"
)).to_equal("navigate-popup:7: _self /next")
expect(_live_default_action(
    mixed_blank, "target-link", "click"
)).to_equal("navigate-popup:6:_BLANK/next")
expect(_live_default_action(
    exact_blank, "target-link", "click"
)).to_equal("navigate-popup:6:_blank/next")
expect(_live_default_action(
    named, "target-link", "click"
)).to_equal("navigate-popup:13:report: frame/next")
expect(_live_default_action(
    mixed_self, "target-link", "click"
)).to_equal("navigate:/next")
expect(_live_default_action(
    exact_self, "target-link", "click"
)).to_equal("navigate:/next")
expect(_live_default_action(
    parent_target, "target-link", "click"
)).to_equal("navigate:/next")
expect(_live_default_action(
    top_target, "target-link", "click"
)).to_equal("navigate:/next")
expect(_live_default_action(
    empty_target, "target-link", "click"
)).to_equal("navigate:/next")

step("Activate whitespace and keyword targets by pointer and Enter")
_act_live_control(
    spaced_self, "link", "Spaced self", "click", ""
)
_act_live_control(
    mixed_blank, "link", "Mixed blank", "key", "Enter"
)
_act_live_control(
    exact_blank, "link", "Exact blank", "click", ""
)
_act_live_control(
    named, "link", "Named target", "click", ""
)
_act_live_control(
    mixed_self, "link", "Mixed self", "key", "Enter"
)
_act_live_control(
    exact_self, "link", "Exact self", "click", ""
)
_act_live_control(
    parent_target, "link", "Parent target", "click", ""
)
_act_live_control(
    top_target, "link", "Top target", "key", "Enter"
)
_act_live_control(
    empty_target, "link", "Empty target", "click", ""
)

step("Fail popup attempts closed and preserve current-target behavior")
expect_target_context_unchanged(
    spaced_self, "CSP sandbox blocked popup"
)
expect_target_context_unchanged(
    mixed_blank, "CSP sandbox blocked popup"
)
expect_target_context_unchanged(
    exact_blank, "CSP sandbox blocked popup"
)
expect_target_context_unchanged(
    named, "popup-context-unavailable"
)
expect_current_target_navigation(mixed_self)
expect_current_target_navigation(exact_self)
expect_current_target_navigation(parent_target)
expect_current_target_navigation(top_target)
expect_current_target_navigation(empty_target)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
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

- Canonical SPipe generation for source `80c6f11828413f8a7d4d40e161529d860e3d7f2e5ae4199313992996b8e8292f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80c6f11828413f8a7d4d40e161529d860e3d7f2e5ae4199313992996b8e8292f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80c6f11828413f8a7d4d40e161529d860e3d7f2e5ae4199313992996b8e8292f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/browser/feature/browser_live_default_action_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_live_default_action_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_live_default_action_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_live_default_action_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_live_default_action_spec.spl:314:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route only the action derived from the live target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_live_default_action_spec.spl:314:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route only the action derived from the live target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/browser_live_default_action_spec.spl:332:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should never coerce a new target into the current document' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_live_default_action_spec.spl:332:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should never coerce a new target into the current document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

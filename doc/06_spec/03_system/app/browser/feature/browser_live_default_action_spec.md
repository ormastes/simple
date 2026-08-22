# Browser live default-action validation

> Verifies the browser live default action behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser live default-action validation

Verifies the browser live default action behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_live_default_action_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser live default action behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### BrowserSession live default actions

#### should route only the action derived from the live target

- Verify: should route only the action derived from the live target
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-021
step("Verify: should route only the action derived from the live target")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should never coerce a new target into the current document
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

Runnable source: 108 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-021 REQ-WEB-BROWSER-012 REQ-WEB-BROWSER-013
step("Verify: should never coerce a new target into the current document")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc787d2298ca1f09045fefaa7cd7b8a20415b22c09da5c2ca9edcc40e3a78b57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc787d2298ca1f09045fefaa7cd7b8a20415b22c09da5c2ca9edcc40e3a78b57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc787d2298ca1f09045fefaa7cd7b8a20415b22c09da5c2ca9edcc40e3a78b57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/app/browser/feature/browser_live_default_action_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_live_default_action_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_live_default_action_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_live_default_action_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_live_default_action_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_live_default_action_spec.spl:324:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route only the action derived from the live target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_live_default_action_spec.spl:343:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should never coerce a new target into the current document' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

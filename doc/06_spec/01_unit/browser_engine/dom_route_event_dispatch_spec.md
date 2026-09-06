# Typed DOM route dispatch

> Route dispatch preserves action order and cancellation without publishing or

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed DOM route dispatch

Route dispatch preserves action order and cancellation without publishing or

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/dom_route_event_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Route dispatch preserves action order and cancellation without publishing or
reparsing text routing identities.

## Scenarios

### Typed DOM route event dispatch

#### keeps typed current-target order and cancellation state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps typed current-target order and cancellation state
   - Expected: dispatch.target_route equals `fixture.target_route`
   - Expected: dispatch.actions equals `[`
   - Expected: dispatch.phases equals `[`
   - Expected: dispatch.current_targets.len() equals `3`
   - Expected: dispatch.current_targets[0] equals `fixture.root_route`
   - Expected: dispatch.current_targets[1] equals `fixture.target_route`
   - Expected: dispatch.current_targets[2] equals `fixture.parent_route`
   - Expected: dispatch.event.namespace_uri equals `urn:test-payload`
   - Expected: dispatch.event.client_x equals `42`
   - Expected: dispatch.event.pointer_type equals `pen`
   - Expected: dispatch.event.target_tag equals `input`
   - Expected: dispatch.event.current_target_tag equals `div`
   - Expected: dispatch.default_action equals `focus-element`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keeps typed current-target order and cancellation state")
val fixture = _route_dispatch_fixture()
val dispatch = be_dom_dispatch_event_to_route(
    fixture.root, fixture.index, fixture.target_route,
    "click", true, true, true, _route_dispatch_executor
)

expect(dispatch.target_route).to_equal(fixture.target_route)
expect(dispatch.related_target_route).to_be_nil()
expect(dispatch.actions).to_equal([
    "root-capture", "cancel", "parent-bubble"
])
expect(dispatch.phases).to_equal([
    "capture", "target", "bubble"
])
expect(dispatch.current_targets.len()).to_equal(3)
expect(dispatch.current_targets[0]).to_equal(fixture.root_route)
expect(dispatch.current_targets[1]).to_equal(fixture.target_route)
expect(dispatch.current_targets[2]).to_equal(fixture.parent_route)
expect(dispatch.event.default_prevented).to_be(true)
expect(dispatch.event.namespace_uri).to_equal("urn:test-payload")
expect(dispatch.event.client_x).to_equal(42)
expect(dispatch.event.pointer_type).to_equal("pen")
expect(dispatch.event.target_tag).to_equal("input")
expect(dispatch.event.current_target_tag).to_equal("div")
expect(dispatch.default_action).to_equal("focus-element")
expect(dispatch.default_action_allowed).to_be(false)
```

</details>

#### returns the typed receipt for keyboard and input payloads

- returns the typed receipt for keyboard and input payloads
   - Expected: keyboard.target_route equals `fixture.target_route`
   - Expected: keyboard.event.key equals `Enter`
   - Expected: keyboard.current_targets.len() equals `1`
   - Expected: keyboard.current_targets[0] equals `fixture.target_route`
   - Expected: input.target_route equals `fixture.target_route`
   - Expected: input.event.input_data equals `Some("x")`
   - Expected: input.event.input_type equals `insertText`
   - Expected: input.current_targets.len() equals `1`
   - Expected: input.current_targets[0] equals `fixture.target_route`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the typed receipt for keyboard and input payloads")
val fixture = _route_dispatch_fixture()
val keyboard = be_dom_dispatch_keyboard_event_to_route(
    fixture.root, fixture.index, fixture.target_route,
    "keydown", true, true, "Enter", "Enter", false, true
)
val input = be_dom_dispatch_input_event_to_route(
    fixture.root, fixture.index, fixture.target_route,
    "input", true, false, Some("x"), "insertText", false, true
)

expect(keyboard.target_route).to_equal(fixture.target_route)
expect(keyboard.event.key).to_equal("Enter")
expect(keyboard.current_targets.len()).to_equal(1)
expect(keyboard.current_targets[0]).to_equal(fixture.target_route)
expect(input.target_route).to_equal(fixture.target_route)
expect(input.event.input_data).to_equal(Some("x"))
expect(input.event.input_type).to_equal("insertText")
expect(input.current_targets.len()).to_equal(1)
expect(input.current_targets[0]).to_equal(fixture.target_route)
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

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-004`
- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `df736b1314a321c2517cfe42a04a0d33a61f5f70112b799c357da0633ee4bc37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df736b1314a321c2517cfe42a04a0d33a61f5f70112b799c357da0633ee4bc37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df736b1314a321c2517cfe42a04a0d33a61f5f70112b799c357da0633ee4bc37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/browser_engine/dom_route_event_dispatch_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/dom_route_event_dispatch_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/browser_engine/dom_route_event_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/dom_route_event_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/dom_route_event_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/dom_route_event_dispatch_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/browser_engine/dom_route_event_dispatch_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps typed current-target order and cancellation state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/dom_route_event_dispatch_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the typed receipt for keyboard and input payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

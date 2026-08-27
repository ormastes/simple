# JS Integration Specification

> Integration tests for REQ-7 / AC-6: a test page exercising setTimeout + addEventListener('click') + DOM mutation, and for AC-2 (dom_bindings wired to BeDomNode).  Also covers AC-1 (ScriptHost + engine integration).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JS Integration Specification

Integration tests for REQ-7 / AC-6: a test page exercising setTimeout + addEventListener('click') + DOM mutation, and for AC-2 (dom_bindings wired to BeDomNode).  Also covers AC-1 (ScriptHost + engine integration).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M15-JS-INTEGRATION |
| Category | Stdlib |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/browser_engine/js_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Integration tests for REQ-7 / AC-6: a test page exercising setTimeout +
addEventListener('click') + DOM mutation, and for AC-2 (dom_bindings wired to
BeDomNode).  Also covers AC-1 (ScriptHost + engine integration).

These tests call `ScriptHost.execute`, which requires the implementation to
exist; all specs FAIL until the full integration is wired.

Note on interpreter-mode limits: cross-module calls to JsInterpreter internals
are NOT tested here. Only ScriptHost's public surface is exercised, which
avoids "value is not callable" interpreter crashes.

## Scenarios

### JS Integration

### AC-6: script host ingests a multi-element page DOM

#### AC-6: execute with a multi-element DOM does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = _make_host_with_page()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-6: dom_root after execute preserves root tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = _make_host_with_page()
val root = host.dom_root()
expect(root.tag).to_equal("html")
```

</details>

### AC-2: getElementById integration — dom_root tree traversal

#### AC-2: be_dom_find_by_id locates button element in page DOM

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_page_dom()
val found = be_dom_find_by_id(root, "my-btn")
expect(found.id).to_equal("my-btn")
```

</details>

#### AC-2: be_dom_find_by_id locates output div by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_page_dom()
val found = be_dom_find_by_id(root, "output")
expect(found.id).to_equal("output")
```

</details>

#### AC-2: be_dom_find_by_id returns nil for absent id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_page_dom()
val found = be_dom_find_by_id(root, "nope")
expect(found).to_be_nil()
```

</details>

### AC-2: querySelector integration — tag and id selectors

#### AC-2: querySelector by tag finds button element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_page_dom()
val found = be_dom_query_selector(root, "button")
expect(found.tag).to_equal("button")
```

</details>

#### AC-2: querySelector by #id finds output div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_page_dom()
val found = be_dom_query_selector(root, "#output")
expect(found.id).to_equal("output")
```

</details>

### AC-6: event injection — no registered listener

#### AC-6: injecting click event with no listener leaves dom_dirty false

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host_with_page()
val event = _make_click_on_btn()
val index = host._dom_identity_index.unwrap()
host.inject_dom_event_route(
    index.route_for_author_id("my-btn").unwrap(), event
).unwrap()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

### AC-3: event loop tick integration

#### AC-3: tick on host with empty DOM after execute does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host_with_page()
host.tick(1000000)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-3: multiple ticks in sequence do not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host_with_page()
host.tick(1000000)
host.tick(2000000)
host.tick(3000000)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

### AC-4: console buffer reachable from integration

#### AC-4: console buffer starts empty after fresh execute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = _make_host_with_page()
val buf = host.console_buffer()
val count = buf.entries().len()
expect(count).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-7`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9453c9eb78066d3db086e7f018b4c292ac847d593f6d380ce2b84edf7ad401a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9453c9eb78066d3db086e7f018b4c292ac847d593f6d380ce2b84edf7ad401a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9453c9eb78066d3db086e7f018b4c292ac847d593f6d380ce2b84edf7ad401a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **80/100**; blockers: **0**.

SSpec documentization score: 80/100
source: test/unit/browser_engine/js_integration_spec.spl
mirror: doc/06_spec/unit/browser_engine/js_integration_spec.md (current)
findings: 11 blockers: 0
  narrative=80 structure=60 oracle=90
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/js_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/js_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/js_integration_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/browser_engine/js_integration_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/unit/browser_engine/js_integration_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/browser_engine/js_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/browser_engine/js_integration_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/unit/browser_engine/js_integration_spec.spl:74:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'AC-6: execute with a multi-element DOM does not crash' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/browser_engine/js_integration_spec.spl:79:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'AC-6: dom_root after execute preserves root tag' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/browser_engine/js_integration_spec.spl:85:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'AC-2: be_dom_find_by_id locates button element in page DOM' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/browser_engine/js_integration_spec.spl:90:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'AC-2: be_dom_find_by_id locates output div by id' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

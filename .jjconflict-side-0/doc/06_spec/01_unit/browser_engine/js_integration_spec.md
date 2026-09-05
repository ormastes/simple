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
| Source | `test/01_unit/browser_engine/js_integration_spec.spl` |
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

- AC-6: execute with a multi-element DOM does not crash
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-6: execute with a multi-element DOM does not crash")
val host = _make_host_with_page()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-6: dom_root after execute preserves root tag

- AC-6: dom_root after execute preserves root tag
   - Expected: root.tag equals `html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-6: dom_root after execute preserves root tag")
val host = _make_host_with_page()
val root = host.dom_root()
expect(root.tag).to_equal("html")
```

</details>

### AC-2: getElementById integration — dom_root tree traversal

#### AC-2: be_dom_find_by_id locates button element in page DOM

- AC-2: be_dom_find_by_id locates button element in page DOM
   - Expected: found.id equals `my-btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-2: be_dom_find_by_id locates button element in page DOM")
val root = _make_page_dom()
val found = be_dom_find_by_id(root, "my-btn")
expect(found.id).to_equal("my-btn")
```

</details>

#### AC-2: be_dom_find_by_id locates output div by id

- AC-2: be_dom_find_by_id locates output div by id
   - Expected: found.id equals `output`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-2: be_dom_find_by_id locates output div by id")
val root = _make_page_dom()
val found = be_dom_find_by_id(root, "output")
expect(found.id).to_equal("output")
```

</details>

#### AC-2: be_dom_find_by_id returns nil for absent id

- AC-2: be_dom_find_by_id returns nil for absent id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-2: be_dom_find_by_id returns nil for absent id")
val root = _make_page_dom()
val found = be_dom_find_by_id(root, "nope")
expect(found).to_be_nil()
```

</details>

### AC-2: querySelector integration — tag and id selectors

#### AC-2: querySelector by tag finds button element

- AC-2: querySelector by tag finds button element
   - Expected: found.tag equals `button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-2: querySelector by tag finds button element")
val root = _make_page_dom()
val found = be_dom_query_selector(root, "button")
expect(found.tag).to_equal("button")
```

</details>

#### AC-2: querySelector by #id finds output div

- AC-2: querySelector by #id finds output div
   - Expected: found.id equals `output`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-2: querySelector by #id finds output div")
val root = _make_page_dom()
val found = be_dom_query_selector(root, "#output")
expect(found.id).to_equal("output")
```

</details>

### AC-6: event injection — no registered listener

#### AC-6: injecting click event with no listener leaves dom_dirty false

- AC-6: injecting click event with no listener leaves dom_dirty false
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-6: injecting click event with no listener leaves dom_dirty false")
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

- AC-3: tick on host with empty DOM after execute does not crash
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: tick on host with empty DOM after execute does not crash")
var host = _make_host_with_page()
host.tick(1000000)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-3: multiple ticks in sequence do not crash

- AC-3: multiple ticks in sequence do not crash
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: multiple ticks in sequence do not crash")
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

- AC-4: console buffer starts empty after fresh execute
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: console buffer starts empty after fresh execute")
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

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-7`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8b531f89955cfe26360aaf8cbc5bc34b28c6bc5bdd4f2b0351842d7df8fc8d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8b531f89955cfe26360aaf8cbc5bc34b28c6bc5bdd4f2b0351842d7df8fc8d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8b531f89955cfe26360aaf8cbc5bc34b28c6bc5bdd4f2b0351842d7df8fc8d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/browser_engine/js_integration_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/js_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/js_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/js_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/js_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/js_integration_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: execute with a multi-element DOM does not crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/js_integration_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: dom_root after execute preserves root tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/js_integration_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: be_dom_find_by_id locates button element in page DOM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

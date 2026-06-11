# JS Integration Specification

> Integration tests for REQ-7 / AC-6: a test page exercising setTimeout + addEventListener('click') + DOM mutation, and for AC-2 (dom_bindings wired to BeDomNode).  Also covers AC-1 (ScriptHost + engine integration).

<!-- sdn-diagram:id=js_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. var host =  make host with page
2. host inject dom event
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host_with_page()
val event = _make_click_on_btn()
host.inject_dom_event(event)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

### AC-3: event loop tick integration

#### AC-3: tick on host with empty DOM after execute does not crash

1. var host =  make host with page
2. host tick
   - Expected: dirty is false


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

1. var host =  make host with page
2. host tick
3. host tick
4. host tick
   - Expected: dirty is false


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

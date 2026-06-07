# ScriptHost Specification

> Tests for `ScriptHost` in `src/lib/gc_async_mut/gpu/browser_engine/script/script_host.spl` (REQ-1 / AC-1). All specs FAIL until that module is implemented.

<!-- sdn-diagram:id=script_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=script_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

script_host_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=script_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ScriptHost Specification

Tests for `ScriptHost` in `src/lib/gc_async_mut/gpu/browser_engine/script/script_host.spl` (REQ-1 / AC-1). All specs FAIL until that module is implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M15-SCRIPT-HOST |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/browser_engine/script/script_host_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `ScriptHost` in
`src/lib/gc_async_mut/gpu/browser_engine/script/script_host.spl` (REQ-1 / AC-1).
All specs FAIL until that module is implemented.

## Key Behaviors

- `ScriptHost.new()` creates a host ready to execute scripts.
- After creation: `dom_dirty()` is false, `console_buffer().entries()` is empty.
- `execute(source, dom_root)` does not panic on an empty script string.
- `dom_dirty()` starts false, `clear_dirty()` resets it.
- `inject_dom_event(event)` accepts a `BeDomEvent` without crashing when no
  listener is registered.
- `tick(now_micros)` can be called without an execute having run first.

## Scenarios

### ScriptHost

### AC-1: lifecycle — creation

#### AC-1: new ScriptHost has dom_dirty false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = _make_host()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: new ScriptHost has empty console buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = _make_host()
val buf = host.console_buffer()
val count = buf.entries().len()
expect(count).to_equal(0)
```

</details>

### AC-1: execute — basic script intake

#### AC-1: execute with empty string does not crash

1. var host =  make host
2. host execute
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
val root = _make_div_root()
host.execute("", root)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: execute_with_type captures transpiled console output

1. var host =  make host
2. host execute with type
   - Expected: entries.len() equals `3`
   - Expected: entries[0].level equals `log`
   - Expected: entries[1].level equals `warn`
   - Expected: entries[2].level equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
val root = _make_div_root()
host.execute_with_type("console.log(\"hello from js\")\nconsole.warn(\"careful\")\nconsole.error(\"bad\")", "text/javascript", root)
val entries = host.console_buffer().entries()
expect(entries.len()).to_equal(3)
expect(entries[0].level).to_equal("log")
expect(entries[0].message).to_contain("hello from js")
expect(entries[1].level).to_equal("warn")
expect(entries[1].message).to_contain("careful")
expect(entries[2].level).to_equal("error")
expect(entries[2].message).to_contain("bad")
```

</details>

### AC-1: dirty flag management

#### AC-1: dom_dirty starts false before any tick

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = _make_host()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: clear_dirty leaves dom_dirty false when already false

1. var host =  make host
2. host clear dirty
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
host.clear_dirty()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

### AC-1: tick — callable without prior execute

#### AC-1: tick with zero timestamp does not crash

1. var host =  make host
2. host tick
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
host.tick(0)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: tick with large timestamp does not crash

1. var host =  make host
2. host tick
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
host.tick(9999999999)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

### AC-1: inject_dom_event — no registered listeners

#### AC-1: inject_dom_event does not crash when no listeners registered

1. var host =  make host
2. host inject dom event
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
val event = _make_click_event()
host.inject_dom_event(event)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: inject_dom_event executes deterministic set-text listener action

1. var host =  make host
2. var root =  make div root
3. root add event listener
4. host execute
5. host inject dom event
   - Expected: host.dom_dirty() is true
   - Expected: host.dom_root().text_content equals `clicked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
var root = _make_div_root()
root.add_event_listener("click", "set-text:clicked")
host.execute("", root)
val event = BeDomEvent.create("click", "div", "", "div", "", true, true)
host.inject_dom_event(event)
expect(host.dom_dirty()).to_equal(true)
expect(host.dom_root().text_content).to_equal("clicked")
```

</details>

#### AC-1: deterministic listener action sets and removes attributes

1. var root =  make div root
2. root = script host apply event action
   - Expected: root.get_attr("aria-expanded") equals `true`
3. root = script host apply event action
   - Expected: root.has_attr("aria-expanded") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = _make_div_root()
root = script_host_apply_event_action(root, "set-attr:aria-expanded=true")
expect(root.get_attr("aria-expanded")).to_equal("true")
root = script_host_apply_event_action(root, "remove-attr:aria-expanded")
expect(root.has_attr("aria-expanded")).to_equal(false)
```

</details>

#### AC-1: deterministic listener action updates class tokens

1. var root =  make div root
2. root = script host apply event action
3. root = script host apply event action
   - Expected: root.classes.len() equals `1`
4. root = script host apply event action
   - Expected: root.classes.len() equals `0`
5. root = script host apply event action
6. root = script host apply event action
   - Expected: root.classes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = _make_div_root()
root = script_host_apply_event_action(root, "add-class:active")
expect(root.classes).to_contain("active")
root = script_host_apply_event_action(root, "add-class:active")
expect(root.classes.len()).to_equal(1)
root = script_host_apply_event_action(root, "toggle-class:active")
expect(root.classes.len()).to_equal(0)
root = script_host_apply_event_action(root, "toggle-class:active")
expect(root.classes).to_contain("active")
root = script_host_apply_event_action(root, "remove-class:active")
expect(root.classes.len()).to_equal(0)
```

</details>

#### AC-1: inject_dom_event executes deterministic attribute and class actions

1. var host =  make host
2. var root =  make div root
3. root add event listener
4. root add event listener
5. host execute
6. host inject dom event
   - Expected: host.dom_root().get_attr("data-clicked") equals `yes`
   - Expected: host.dom_dirty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
var root = _make_div_root()
root.add_event_listener("click", "set-attr:data-clicked=yes")
root.add_event_listener("click", "add-class:clicked")
host.execute("", root)
val event = BeDomEvent.create("click", "div", "", "div", "", true, true)
host.inject_dom_event(event)
expect(host.dom_root().get_attr("data-clicked")).to_equal("yes")
expect(host.dom_root().classes).to_contain("clicked")
expect(host.dom_dirty()).to_equal(true)
```

</details>

### AC-1: dom_root — returns current root

#### AC-1: dom_root after execute returns a BeDomNode

1. var host =  make host
2. host execute
   - Expected: returned_root.tag equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
val root = _make_div_root()
host.execute("", root)
val returned_root = host.dom_root()
expect(returned_root.tag).to_equal("div")
```

</details>

### fetch dispatch bridge

#### uses safe fallback when no fetch dispatch is installed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = _make_host()
val resp = host.fetch(fetch_create_request("https://example.test/data", "GET"))
expect(resp.status).to_equal(0)
expect(resp.ok).to_equal(false)
```

</details>

#### sends fetch requests through installed dispatch

1. var host =  make host
2. host set fetch dispatch
   - Expected: resp.status equals `200`
   - Expected: resp.ok is true
   - Expected: resp.headers[0] equals `x-host`
   - Expected: resp.headers[1] equals `yes`
   - Expected: resp.body equals `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = _make_host()
host.set_fetch_dispatch(ScriptStaticFetchDispatch.create(200, "x-host: yes", "body"))
val resp = host.fetch(fetch_create_request("https://example.test/data", "GET"))
expect(resp.status).to_equal(200)
expect(resp.ok).to_equal(true)
expect(resp.headers[0]).to_equal("x-host")
expect(resp.headers[1]).to_equal("yes")
expect(resp.body).to_equal("body")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

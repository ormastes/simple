# Simple Script Specification

> 1. var exec =  executor

<!-- sdn-diagram:id=simple_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Script Specification

## Scenarios

### SimpleScriptExecutor

#### marks non-empty source execution as dirty and stores the DOM root

1. var exec =  executor
2. exec execute
   - Expected: exec.dom_dirty() is true
   - Expected: exec.dom_root().tag equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = _executor()
val root = BeDomNode.element("main")
exec.execute("console_log(\"hello\")", root)
expect(exec.dom_dirty()).to_equal(true)
expect(exec.dom_root().tag).to_equal("main")
```

</details>

#### drains timer and raf callback slots on tick

1. var event loop = EventLoop new
2. event loop schedule timer
3. event loop schedule raf
4. var exec = SimpleScriptExecutor new
5. exec tick
   - Expected: exec.dom_dirty() is true
   - Expected: exec.event_loop().pending_timer_count() equals `0`
   - Expected: exec.event_loop().pending_raf_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var event_loop = EventLoop.new()
event_loop.schedule_timer(7, 10, 0)
event_loop.schedule_raf(8)
var exec = SimpleScriptExecutor.new(event_loop, ConsoleBuffer.new())
exec.tick(10)
expect(exec.dom_dirty()).to_equal(true)
expect(exec.event_loop().pending_timer_count()).to_equal(0)
expect(exec.event_loop().pending_raf_count()).to_equal(0)
```

</details>

#### runs deterministic listener actions during DOM event injection

1. var exec =  executor
2. var root = BeDomNode element
3. root add event listener
4. root add event listener
5. exec execute
6. exec inject dom event
   - Expected: exec.dom_dirty() is true
   - Expected: exec.dom_root().get_attr("data-clicked") equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = _executor()
var root = BeDomNode.element("div")
root.add_event_listener("click", "set-attr:data-clicked=yes")
root.add_event_listener("click", "add-class:clicked")
exec.execute("", root)
val event = BeDomEvent.create("click", "div", "", "div", "", true, true)
exec.inject_dom_event(event)
expect(exec.dom_dirty()).to_equal(true)
expect(exec.dom_root().get_attr("data-clicked")).to_equal("yes")
expect(exec.dom_root().classes).to_contain("clicked")
```

</details>

#### uses safe fetch fallback without a dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exec = _executor()
val resp = exec.fetch(fetch_create_request("https://example.test/data", "GET"))
expect(resp.status).to_equal(0)
expect(resp.ok).to_equal(false)
```

</details>

#### sends fetch requests through installed dispatch

1. var exec =  executor
2. exec set fetch dispatch
   - Expected: resp.status equals `201`
   - Expected: resp.ok is true
   - Expected: resp.headers[0] equals `x-exec`
   - Expected: resp.headers[1] equals `yes`
   - Expected: resp.body equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = _executor()
exec.set_fetch_dispatch(ScriptStaticFetchDispatch.create(201, "x-exec: yes", "created"))
val resp = exec.fetch(fetch_create_request("https://example.test/data", "POST"))
expect(resp.status).to_equal(201)
expect(resp.ok).to_equal(true)
expect(resp.headers[0]).to_equal("x-exec")
expect(resp.headers[1]).to_equal("yes")
expect(resp.body).to_equal("created")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/script/simple_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleScriptExecutor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

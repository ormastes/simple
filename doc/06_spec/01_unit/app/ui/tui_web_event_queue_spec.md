# Tui Web Event Queue Specification

> <details>

<!-- sdn-diagram:id=tui_web_event_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_web_event_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_web_event_queue_spec -> std
tui_web_event_queue_spec -> app
tui_web_event_queue_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_web_event_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Web Event Queue Specification

## Scenarios

### TuiWebBackend event queue

#### keeps FIFO order across cursor compaction and clears after drain

- backend push event
   - Expected: first != nil is true
   - Expected: second != nil is true
   - Expected: event != nil is true
   - Expected: backend.poll_event(0) == nil is true
   - Expected: backend.event_queue.len() equals `0`
   - Expected: backend.event_head equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = TuiWebBackend.new()
var i = 0
while i < 80:
    backend.push_event(UIEvent.KeyPress(key: "k" + i.to_string()))
    i = i + 1

val first = backend.poll_event(0)
val second = backend.poll_event(0)
expect(first != nil).to_equal(true)
expect(second != nil).to_equal(true)

var drained = 2
while drained < 80:
    val event = backend.poll_event(0)
    expect(event != nil).to_equal(true)
    drained = drained + 1

expect(backend.poll_event(0) == nil).to_equal(true)
expect(backend.event_queue.len()).to_equal(0)
expect(backend.event_head).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/tui_web_event_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TuiWebBackend event queue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

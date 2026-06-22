# Event Queue Specification

> <details>

<!-- sdn-diagram:id=event_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=event_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

event_queue_spec -> std
event_queue_spec -> app
event_queue_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=event_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Event Queue Specification

## Scenarios

### EventQueue via NoneBackend

#### starts with no events

- Ok
   - Expected: event == nil is true
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        val event = backend.poll_event(0)
        expect(event == nil).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### injects and polls a single event

- Ok
- backend inject event
   - Expected: event != nil is true
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        backend.inject_event(UIEvent.Quit)
        val event = backend.poll_event(0)
        expect(event != nil).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### injects multiple events and polls in FIFO order

- Ok
- backend inject events
   - Expected: e1 != nil is true
   - Expected: e2 != nil is true
   - Expected: e3 != nil is true
   - Expected: e4 == nil is true
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        val events = [UIEvent.KeyPress(key: "a"), UIEvent.KeyPress(key: "b"), UIEvent.Quit]
        backend.inject_events(events)

        val e1 = backend.poll_event(0)
        val e2 = backend.poll_event(0)
        val e3 = backend.poll_event(0)
        val e4 = backend.poll_event(0)

        expect(e1 != nil).to_equal(true)
        expect(e2 != nil).to_equal(true)
        expect(e3 != nil).to_equal(true)
        expect(e4 == nil).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### drains long injected event batches without changing visible queue state

- Ok
- events push
- backend inject events
   - Expected: backend.event_queue.len() equals `80`
- UIEvent KeyPress
   - Expected: key equals `"k" + drained.to_string()`
   - Expected: drained equals `-1`
   - Expected: backend.event_queue.len() equals `0`
- Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        var events: [UIEvent] = []
        var i = 0
        while i < 80:
            events.push(UIEvent.KeyPress(key: "k" + i.to_string()))
            i = i + 1
        backend.inject_events(events)

        expect(backend.event_queue.len()).to_equal(80)

        var drained = 0
        while drained < 80:
            val event = backend.poll_event(0)
            match event:
                UIEvent.KeyPress(key) =>
                    expect(key).to_equal("k" + drained.to_string())
                _ =>
                    expect(drained).to_equal(-1)
            drained = drained + 1

        expect(backend.poll_event(0)).to_be_nil()
        expect(backend.event_queue.len()).to_equal(0)
    Err(e) =>
        expect(e).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/event_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- EventQueue via NoneBackend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

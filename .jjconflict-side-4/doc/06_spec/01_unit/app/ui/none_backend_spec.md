# None Backend Specification

> 1. Ok

<!-- sdn-diagram:id=none_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=none_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

none_backend_spec -> std
none_backend_spec -> app
none_backend_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=none_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# None Backend Specification

## Scenarios

### NoneBackend Lifecycle

#### creates successfully

1. Ok
   - Expected: true is true
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        expect(true).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### initializes and shuts down

1. Ok
2. backend shutdown
   - Expected: true is true
3. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        val init_result = backend.init()
        backend.shutdown()
        expect(true).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### NoneBackend Event Injection

#### returns nil when no events queued

1. Ok
   - Expected: event == nil is true
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        val event = backend.poll_event(100)
        expect(event == nil).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### injects and polls a single event

1. Ok
2. backend inject event
   - Expected: event != nil is true
3. Err
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

#### injects multiple events

1. Ok
2. backend inject events
   - Expected: e1 != nil is true
   - Expected: e2 != nil is true
   - Expected: e3 == nil is true
3. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        val events = [UIEvent.KeyPress(key: "a"), UIEvent.KeyPress(key: "b")]
        backend.inject_events(events)
        val e1 = backend.poll_event(0)
        val e2 = backend.poll_event(0)
        val e3 = backend.poll_event(0)
        expect(e1 != nil).to_equal(true)
        expect(e2 != nil).to_equal(true)
        expect(e3 == nil).to_equal(true)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### NoneBackend Render Capture

#### starts with zero render count

1. Ok
   - Expected: backend.render_count() equals `0`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        expect(backend.render_count()).to_equal(0)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### starts with empty last_html

1. Ok
   - Expected: backend.last_html() equals ``
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        expect(backend.last_html()).to_equal("")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### html_at returns empty for out of bounds

1. Ok
   - Expected: backend.html_at(-1) equals ``
   - Expected: backend.html_at(0) equals ``
   - Expected: backend.html_at(100) equals ``
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        expect(backend.html_at(-1)).to_equal("")
        expect(backend.html_at(0)).to_equal("")
        expect(backend.html_at(100)).to_equal("")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### NoneBackend Viewport

#### has default viewport 80x24

1. Ok
   - Expected: backend.viewport_width() equals `80`
   - Expected: backend.viewport_height() equals `24`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        expect(backend.viewport_width()).to_equal(80)
        expect(backend.viewport_height()).to_equal(24)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### allows setting custom viewport

1. Ok
2. backend set viewport
   - Expected: backend.viewport_width() equals `120`
   - Expected: backend.viewport_height() equals `40`
3. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        backend.set_viewport(120, 40)
        expect(backend.viewport_width()).to_equal(120)
        expect(backend.viewport_height()).to_equal(40)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### NoneBackend Capabilities

#### reports all capabilities as false

1. Ok
   - Expected: backend.supports_mouse() is false
   - Expected: backend.supports_color() is false
   - Expected: backend.supports_images() is false
   - Expected: backend.supports_touch() is false
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        expect(backend.supports_mouse()).to_equal(false)
        expect(backend.supports_color()).to_equal(false)
        expect(backend.supports_images()).to_equal(false)
        expect(backend.supports_touch()).to_equal(false)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### reports backend name as none

1. Ok
   - Expected: backend.backend_name() equals `none`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NoneBackend.new()
match result:
    Ok(backend) =>
        expect(backend.backend_name()).to_equal("none")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/none_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NoneBackend Lifecycle
- NoneBackend Event Injection
- NoneBackend Render Capture
- NoneBackend Viewport
- NoneBackend Capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Async Ipc Specification

> 1. ch send

<!-- sdn-diagram:id=async_ipc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_ipc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_ipc_spec -> std
async_ipc_spec -> common
async_ipc_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_ipc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Ipc Specification

## Scenarios

### IPC reader pushes parsed events to channel

#### sends KeyPress event parsed from JSON to channel

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val event = parse_ipc_message(json)
if event != nil:
    ch.send(event)
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### sends Quit event parsed from JSON to channel

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val json = "{\"type\":\"quit\"}"
val event = parse_ipc_message(json)
if event != nil:
    ch.send(event)
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### sends Action event parsed from JSON to channel

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val json = "{\"type\":\"action\",\"name\":\"save\"}"
val event = parse_ipc_message(json)
if event != nil:
    ch.send(event)
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### parses common WebRender input key envelopes

1. UIEvent KeyPress
   - Expected: key equals `Enter`
   - Expected: "expected key input envelope" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"input\",\"target\":\"tauri\",\"surface_id\":\"main\",\"event_type\":\"key\",\"target_id\":\"\",\"key\":\"Enter\",\"value\":\"\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val event = parse_ipc_message(json)
match event:
    UIEvent.KeyPress(key) =>
        expect(key).to_equal("Enter")
    _ =>
        expect("expected key input envelope").to_equal("")
```

</details>

#### parses common WebRender input action and resize envelopes

1. UIEvent Action
   - Expected: name equals `save`
   - Expected: "expected action input envelope" equals ``
2. UIEvent Resize
   - Expected: width equals `640`
   - Expected: height equals `480`
   - Expected: "expected resize input envelope" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val action_json = "{\"type\":\"input\",\"target\":\"tauri\",\"surface_id\":\"main\",\"event_type\":\"action\",\"target_id\":\"\",\"key\":\"\",\"value\":\"save\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val action_event = parse_ipc_message(action_json)
match action_event:
    UIEvent.Action(name) =>
        expect(name).to_equal("save")
    _ =>
        expect("expected action input envelope").to_equal("")

val resize_json = "{\"type\":\"input\",\"target\":\"tauri\",\"surface_id\":\"main\",\"event_type\":\"resize\",\"target_id\":\"\",\"key\":\"\",\"value\":\"\",\"x\":640,\"y\":480,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val resize_event = parse_ipc_message(resize_json)
match resize_event:
    UIEvent.Resize(width, height) =>
        expect(width).to_equal(640)
        expect(height).to_equal(480)
    _ =>
        expect("expected resize input envelope").to_equal("")
```

</details>

#### parses Electron bridge common input envelopes

1. UIEvent KeyPress
   - Expected: key equals `Enter`
   - Expected: "expected electron key input envelope" equals ``
2. UIEvent Resize
   - Expected: width equals `640`
   - Expected: height equals `480`
   - Expected: "expected electron resize input envelope" equals ``
3. UIEvent InputChange
   - Expected: target_id equals `name`
   - Expected: value equals `Ada`
   - Expected: "expected electron text input envelope" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_json = "{\"type\":\"input\",\"target\":\"electron\",\"surface_id\":\"main\",\"event_type\":\"key\",\"target_id\":\"\",\"key\":\"Enter\",\"value\":\"\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val key_event = parse_ipc_message(key_json)
match key_event:
    UIEvent.KeyPress(key) =>
        expect(key).to_equal("Enter")
    _ =>
        expect("expected electron key input envelope").to_equal("")

val resize_json = "{\"type\":\"input\",\"target\":\"electron\",\"surface_id\":\"main\",\"event_type\":\"resize\",\"target_id\":\"\",\"key\":\"\",\"value\":\"\",\"x\":640,\"y\":480,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val resize_event = parse_ipc_message(resize_json)
match resize_event:
    UIEvent.Resize(width, height) =>
        expect(width).to_equal(640)
        expect(height).to_equal(480)
    _ =>
        expect("expected electron resize input envelope").to_equal("")

val input_json = "{\"type\":\"input\",\"target\":\"electron\",\"surface_id\":\"main\",\"event_type\":\"input\",\"target_id\":\"name\",\"key\":\"\",\"value\":\"Ada\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val input_event = parse_ipc_message(input_json)
match input_event:
    UIEvent.InputChange(target_id, value) =>
        expect(target_id).to_equal("name")
        expect(value).to_equal("Ada")
    _ =>
        expect("expected electron text input envelope").to_equal("")
```

</details>

### IPC writer sends render messages

#### build_ipc_render wraps html in render JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<div>Hello Async</div>"
val msg = build_ipc_render(html)
expect(msg).to_contain("\"type\":\"render\"")
expect(msg).to_contain("Hello Async")
```

</details>

#### writer preserves common WebRender artifact IPC JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "{\"type\":\"render\",\"target\":\"electron\",\"surface_id\":\"main\",\"width\":1280,\"height\":720,\"html\":\"<div></div>\"}"
expect(ipc_writer_message(msg)).to_equal(msg)
```

</details>

#### writer wraps legacy raw HTML for compatibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = ipc_writer_message("<div>Legacy</div>")
expect(msg).to_contain("\"type\":\"render\"")
expect(msg).to_contain("Legacy")
```

</details>

#### render channel can queue multiple messages

1. ch send
2. ch send
   - Expected: first equals `<p>First</p>`
   - Expected: second equals `<p>Second</p>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send("<p>First</p>")
ch.send("<p>Second</p>")
val first = ch.try_recv()
val second = ch.try_recv()
expect(first).to_equal("<p>First</p>")
expect(second).to_equal("<p>Second</p>")
```

</details>

### Quit message stops reader

#### quit event is recognized by parse_ipc_message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"quit\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
```

</details>

#### channel receives quit then reader can stop

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val json = "{\"type\":\"quit\"}"
val event = parse_ipc_message(json)
if event != nil:
    ch.send(event)
# Simulate reader checking for quit
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

### Invalid JSON handled gracefully

#### returns nil for garbage input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("not json at all")
expect(event == nil).to_equal(true)
```

</details>

#### returns nil for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("")
expect(event == nil).to_equal(true)
```

</details>

#### returns nil for unknown type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"foobar\",\"data\":\"xyz\"}"
val event = parse_ipc_message(json)
expect(event == nil).to_equal(true)
```

</details>

#### returns nil for partial JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":")
expect(event == nil).to_equal(true)
```

</details>

#### does not push nil events to channel

1. ch send
   - Expected: received == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val event = parse_ipc_message("garbage")
if event != nil:
    ch.send(event)
val received = ch.try_recv()
expect(received == nil).to_equal(true)
```

</details>

### Channel close stops reader

#### closed channel reports is_closed true

1. ch close
   - Expected: ch.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
expect(ch.is_closed()).to_equal(true)
```

</details>

#### can try_recv before close returns nil when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val received = ch.try_recv()
expect(received == nil).to_equal(true)
```

</details>

#### can try_recv buffered message before close

1. ch send
   - Expected: received equals `buffered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send("buffered")
val received = ch.try_recv()
expect(received).to_equal("buffered")
```

</details>

#### closed channel is_closed returns true

1. ch close
   - Expected: after is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val before = ch.is_closed()
expect(before).to_equal(false)
ch.close()
val after = ch.is_closed()
expect(after).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/async_ipc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPC reader pushes parsed events to channel
- IPC writer sends render messages
- Quit message stops reader
- Invalid JSON handled gracefully
- Channel close stops reader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

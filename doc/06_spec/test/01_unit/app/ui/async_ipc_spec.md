# Async Ipc Specification

> <details>

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

- Some
- key ch send
- pass dn
   - Expected: key_received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_ch = channel_new()
val key_json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val key_event = parse_ipc_message(key_json)
match key_event:
    Some(parsed):
        key_ch.send(parsed)
    nil:
        pass_dn("parse failed")
val key_received = key_ch.try_recv()
expect(key_received != nil).to_equal(true)
```

</details>

#### sends Quit event parsed from JSON to channel

- Some
- quit ch send
- pass dn
   - Expected: quit_received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quit_ch = channel_new()
val quit_json = "{\"type\":\"quit\"}"
val quit_event = parse_ipc_message(quit_json)
match quit_event:
    Some(parsed):
        quit_ch.send(parsed)
    nil:
        pass_dn("parse failed")
val quit_received = quit_ch.try_recv()
expect(quit_received != nil).to_equal(true)
```

</details>

#### sends Action event parsed from JSON to channel

- Some
- action ch send
- pass dn
   - Expected: action_received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val action_ch = channel_new()
val action_direct_json = "{\"type\":\"action\",\"name\":\"save\"}"
val action_direct_event = parse_ipc_message(action_direct_json)
match action_direct_event:
    Some(parsed):
        action_ch.send(parsed)
    nil:
        pass_dn("parse failed")
val action_received = action_ch.try_recv()
expect(action_received != nil).to_equal(true)
```

</details>

#### parses common WebRender input key envelopes

- Some
- UIEvent KeyPress
   - Expected: key equals `Enter`
   - Expected: "expected key input envelope" equals ``
   - Expected: "expected key input envelope" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_env_json = "{\"type\":\"input\",\"target\":\"tauri\",\"surface_id\":\"main\",\"event_type\":\"key\",\"target_id\":\"\",\"key\":\"Enter\",\"value\":\"\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val key_env_event = parse_ipc_message(key_env_json)
expect(key_env_event != nil).to_equal(true)
match key_env_event:
    Some(parsed):
        match parsed:
            UIEvent.KeyPress(key):
                expect(key).to_equal("Enter")
            _:
                expect("expected key input envelope").to_equal("")
    nil:
        expect("expected key input envelope").to_equal("")
```

</details>

#### parses common WebRender input action and resize envelopes

- Some
- UIEvent Action
   - Expected: name equals `save`
   - Expected: "expected action input envelope" equals ``
   - Expected: "expected action input envelope" equals ``
   - Expected: resize_env_event != nil is true
- Some
- UIEvent Resize
   - Expected: width equals `640`
   - Expected: height equals `480`
   - Expected: "expected resize input envelope" equals ``
   - Expected: "expected resize input envelope" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val action_json = "{\"type\":\"input\",\"target\":\"tauri\",\"surface_id\":\"main\",\"event_type\":\"action\",\"target_id\":\"\",\"key\":\"\",\"value\":\"save\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val action_event = parse_ipc_message(action_json)
expect(action_event != nil).to_equal(true)
match action_event:
    Some(parsed_action):
        match parsed_action:
            UIEvent.Action(name):
                expect(name).to_equal("save")
            _:
                expect("expected action input envelope").to_equal("")
    nil:
        expect("expected action input envelope").to_equal("")

val resize_env_json = "{\"type\":\"input\",\"target\":\"tauri\",\"surface_id\":\"main\",\"event_type\":\"resize\",\"target_id\":\"\",\"key\":\"\",\"value\":\"\",\"x\":640,\"y\":480,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val resize_env_event = parse_ipc_message(resize_env_json)
expect(resize_env_event != nil).to_equal(true)
match resize_env_event:
    Some(parsed_resize):
        match parsed_resize:
            UIEvent.Resize(width, height):
                expect(width).to_equal(640)
                expect(height).to_equal(480)
            _:
                expect("expected resize input envelope").to_equal("")
    nil:
        expect("expected resize input envelope").to_equal("")
```

</details>

#### parses Electron bridge common input envelopes

- Some
- UIEvent KeyPress
   - Expected: key equals `Enter`
   - Expected: "expected electron key input envelope" equals ``
   - Expected: "expected electron key input envelope" equals ``
   - Expected: electron_resize_event != nil is true
- Some
- UIEvent Resize
   - Expected: width equals `640`
   - Expected: height equals `480`
   - Expected: "expected electron resize input envelope" equals ``
   - Expected: "expected electron resize input envelope" equals ``
   - Expected: electron_input_event != nil is true
- Some
- UIEvent InputChange
   - Expected: target_id equals `name`
   - Expected: value equals `Ada`
   - Expected: "expected electron text input envelope" equals ``
   - Expected: "expected electron text input envelope" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val electron_key_json = "{\"type\":\"input\",\"target\":\"electron\",\"surface_id\":\"main\",\"event_type\":\"key\",\"target_id\":\"\",\"key\":\"Enter\",\"value\":\"\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val electron_key_event = parse_ipc_message(electron_key_json)
expect(electron_key_event != nil).to_equal(true)
match electron_key_event:
    Some(parsed_key):
        match parsed_key:
            UIEvent.KeyPress(key):
                expect(key).to_equal("Enter")
            _:
                expect("expected electron key input envelope").to_equal("")
    nil:
        expect("expected electron key input envelope").to_equal("")

val electron_resize_json = "{\"type\":\"input\",\"target\":\"electron\",\"surface_id\":\"main\",\"event_type\":\"resize\",\"target_id\":\"\",\"key\":\"\",\"value\":\"\",\"x\":640,\"y\":480,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val electron_resize_event = parse_ipc_message(electron_resize_json)
expect(electron_resize_event != nil).to_equal(true)
match electron_resize_event:
    Some(parsed_resize):
        match parsed_resize:
            UIEvent.Resize(width, height):
                expect(width).to_equal(640)
                expect(height).to_equal(480)
            _:
                expect("expected electron resize input envelope").to_equal("")
    nil:
        expect("expected electron resize input envelope").to_equal("")

val electron_input_json = "{\"type\":\"input\",\"target\":\"electron\",\"surface_id\":\"main\",\"event_type\":\"input\",\"target_id\":\"name\",\"key\":\"\",\"value\":\"Ada\",\"x\":0,\"y\":0,\"dx\":0,\"dy\":0,\"button\":\"\"}"
val electron_input_event = parse_ipc_message(electron_input_json)
expect(electron_input_event != nil).to_equal(true)
match electron_input_event:
    Some(parsed_input):
        match parsed_input:
            UIEvent.InputChange(target_id, value):
                expect(target_id).to_equal("name")
                expect(value).to_equal("Ada")
            _:
                expect("expected electron text input envelope").to_equal("")
    nil:
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
val render_html_fixture = "<div>Hello Async</div>"
val render_msg = build_ipc_render(render_html_fixture)
expect(render_msg).to_contain("\"type\":\"render\"")
expect(render_msg).to_contain("Hello Async")
```

</details>

#### writer preserves common WebRender artifact IPC JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact_msg = "{\"type\":\"render\",\"target\":\"electron\",\"surface_id\":\"main\",\"width\":1280,\"height\":720,\"html\":\"<div></div>\"}"
expect(ipc_writer_message(artifact_msg)).to_equal(artifact_msg)
```

</details>

#### writer wraps legacy raw HTML for compatibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy_msg = ipc_writer_message("<div>Legacy</div>")
expect(legacy_msg).to_contain("\"type\":\"render\"")
expect(legacy_msg).to_contain("Legacy")
```

</details>

#### render channel can queue multiple messages

- render ch send
- render ch send
   - Expected: first_render_payload != nil is true
   - Expected: second_render_payload != nil is true
- Some
   - Expected: first_value equals `<p>First</p>`
   - Expected: "expected first buffered message" equals ``
- Some
   - Expected: second_value equals `<p>Second</p>`
   - Expected: "expected second buffered message" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val render_ch = channel_new()
render_ch.send("<p>First</p>")
render_ch.send("<p>Second</p>")
val first_render_payload = render_ch.try_recv()
val second_render_payload = render_ch.try_recv()
expect(first_render_payload != nil).to_equal(true)
expect(second_render_payload != nil).to_equal(true)
match first_render_payload:
    Some(first_value):
        expect(first_value).to_equal("<p>First</p>")
    nil:
        expect("expected first buffered message").to_equal("")
match second_render_payload:
    Some(second_value):
        expect(second_value).to_equal("<p>Second</p>")
    nil:
        expect("expected second buffered message").to_equal("")
```

</details>

### Quit message stops reader

#### quit event is recognized by parse_ipc_message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quit_recognition_json = "{\"type\":\"quit\"}"
val quit_recognition_event = parse_ipc_message(quit_recognition_json)
expect(quit_recognition_event != nil).to_equal(true)
```

</details>

#### channel receives quit then reader can stop

- Some
- quit stop ch send
- pass dn
   - Expected: quit_stop_received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quit_stop_ch = channel_new()
val quit_stop_json = "{\"type\":\"quit\"}"
val quit_stop_event = parse_ipc_message(quit_stop_json)
match quit_stop_event:
    Some(parsed):
        quit_stop_ch.send(parsed)
    nil:
        pass_dn("parse failed")
# Simulate reader checking for quit
val quit_stop_received = quit_stop_ch.try_recv()
expect(quit_stop_received != nil).to_equal(true)
```

</details>

### Invalid JSON handled gracefully

#### returns nil for garbage input

- Some
   - Expected: "expected garbage input to be dropped" equals ``
- pass dn


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val garbage_event = parse_ipc_message("not json at all")
match garbage_event:
    Some(_):
        expect("expected garbage input to be dropped").to_equal("")
    nil:
        pass_dn("invalid input dropped")
```

</details>

#### returns nil for empty string

- Some
   - Expected: "expected empty input to be dropped" equals ``
- pass dn


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_event = parse_ipc_message("")
match empty_event:
    Some(_):
        expect("expected empty input to be dropped").to_equal("")
    nil:
        pass_dn("empty input dropped")
```

</details>

#### returns nil for unknown type

- Some
   - Expected: "expected unknown type to be dropped" equals ``
- pass dn


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unknown_type_json = "{\"type\":\"foobar\",\"data\":\"xyz\"}"
val unknown_type_event = parse_ipc_message(unknown_type_json)
match unknown_type_event:
    Some(_):
        expect("expected unknown type to be dropped").to_equal("")
    nil:
        pass_dn("unknown type dropped")
```

</details>

#### returns nil for partial JSON

- Some
   - Expected: "expected partial JSON to be dropped" equals ``
- pass dn


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val partial_event = parse_ipc_message("{\"type\":")
match partial_event:
    Some(_):
        expect("expected partial JSON to be dropped").to_equal("")
    nil:
        pass_dn("partial JSON dropped")
```

</details>

#### does not push nil events to channel

- Some
- nil event ch send
- pass dn
   - Expected: nil_push_received == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nil_event_ch = channel_new()
val nil_push_event = parse_ipc_message("garbage")
match nil_push_event:
    Some(parsed):
        nil_event_ch.send(parsed)
    nil:
        pass_dn("parse failed")
val nil_push_received = nil_event_ch.try_recv()
expect(nil_push_received == nil).to_equal(true)
```

</details>

### Channel close stops reader

#### closed channel reports is_closed true

- close ch close
   - Expected: close_ch.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val close_ch = channel_new()
close_ch.close()
expect(close_ch.is_closed()).to_equal(true)
```

</details>

#### can try_recv before close returns nil when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_ch = channel_new()
val empty_received = empty_ch.try_recv()
expect(empty_received == nil).to_equal(true)
```

</details>

#### can try_recv buffered message before close

- buffered ch send
   - Expected: buffered_received != nil is true
- Some
   - Expected: value equals `buffered`
   - Expected: "expected buffered value" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buffered_ch = channel_new()
buffered_ch.send("buffered")
val buffered_received = buffered_ch.try_recv()
expect(buffered_received != nil).to_equal(true)
match buffered_received:
    Some(value):
        expect(value).to_equal("buffered")
    nil:
        expect("expected buffered value").to_equal("")
```

</details>

#### closed channel is_closed returns true

- close state ch close
   - Expected: after is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val close_state_ch = channel_new()
val before = close_state_ch.is_closed()
expect(before).to_equal(false)
close_state_ch.close()
val after = close_state_ch.is_closed()
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

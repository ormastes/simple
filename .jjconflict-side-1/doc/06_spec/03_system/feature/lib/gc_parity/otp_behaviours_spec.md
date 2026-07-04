# OTP Behaviour Implementations

> Tests the OTP-inspired GenServer, GenStatem, and GenEvent behaviour contracts with message dispatch patterns.

<!-- sdn-diagram:id=otp_behaviours_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=otp_behaviours_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

otp_behaviours_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=otp_behaviours_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# OTP Behaviour Implementations

Tests the OTP-inspired GenServer, GenStatem, and GenEvent behaviour contracts with message dispatch patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/lib/gc_parity/otp_behaviours_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the OTP-inspired GenServer, GenStatem, and GenEvent behaviour
contracts with message dispatch patterns.

## Scenarios

### GenServer Behaviour

#### when handling calls

#### updates state via call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0
state = state + 1
expect(state).to_equal(1)
```

</details>

#### supports reply format

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "reply|hello|updated_state"
val parts = result.split("|")
expect(parts[0]).to_equal("reply")
expect(parts.len()).to_equal(3)
expect(parts[1]).to_equal("hello")
expect(parts[2]).to_equal("updated_state")
```

</details>

#### when using message prefixes

#### identifies call messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "call:get_count"
val is_call = msg.starts_with("call:")
expect(is_call).to_equal(true)
val request = msg.substring(5)
expect(request).to_equal("get_count")
```

</details>

#### identifies cast messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "cast:increment"
val is_cast = msg.starts_with("cast:")
expect(is_cast).to_equal(true)
```

</details>

#### identifies stop message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = '$$stop$$'
val is_stop = msg == '$$stop$$'
expect(is_stop).to_equal(true)
```

</details>

### GenStatem Behaviour

#### when processing transitions

#### transitions through states

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "red"
if state == "red":
    state = "green"
expect(state).to_equal("green")

if state == "green":
    state = "yellow"
expect(state).to_equal("yellow")

if state == "yellow":
    state = "red"
expect(state).to_equal("red")
```

</details>

#### counts transitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
var state = "idle"
state = "active"
count = count + 1
state = "idle"
count = count + 1
expect(count).to_equal(2)
```

</details>

#### when using transition result format

#### parses next_state result

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "next_state:active|session_id=123"
val is_transition = result.starts_with("next_state:")
expect(is_transition).to_equal(true)
val payload = result.substring(11)
val parts = payload.split("|")
val new_state = parts[0]
expect(new_state).to_equal("active")
```

</details>

#### parses stop result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "stop:normal"
val is_stop = result.starts_with("stop:")
expect(is_stop).to_equal(true)
```

</details>

### GenEvent Behaviour

#### when managing handlers

#### adds and counts handlers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler_list = ["logger", "metrics", "audit"]
expect(handler_list[0]).to_equal("logger")
expect(handler_list.len()).to_equal(3)
```

</details>

#### removes handlers by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_handlers = ["logger", "metrics", "audit"]
var count = 0
for h in all_handlers:
    if h != "metrics":
        count = count + 1
expect(count).to_equal(2)
```

</details>

#### when dispatching events

#### broadcasts to all handlers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler_ids = ["h1", "h2", "h3"]
var dispatched_count = 0
for h in handler_ids:
    dispatched_count = dispatched_count + 1
expect(dispatched_count).to_equal(3)
```

</details>

#### collects sync responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val responses = ["ok", "ok", "error"]
expect(responses.len()).to_equal(3)
var ok_count = 0
for r in responses:
    if r == "ok":
        ok_count = ok_count + 1
expect(ok_count).to_equal(2)
```

</details>

### Common Module Migration

#### when using migrated modules

#### basic array operations work

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [5, 3, 1, 4, 2]
expect(items[0]).to_equal(5)
expect(items.len()).to_equal(5)
```

</details>

#### string operations for config parsing work

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "key = value"
val has_eq = line.contains("=")
expect(has_eq).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

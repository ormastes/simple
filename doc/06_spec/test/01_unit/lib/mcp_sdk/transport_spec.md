# Transport Specification

> <details>

<!-- sdn-diagram:id=transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transport Specification

## Scenarios

### BufferTransport - construction

#### new() creates an empty transport

- var bt = BufferTransport new
   - Expected: sc equals `0`
   - Expected: ic equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
val sc = bt.sent_count()
val ic = bt.inbound_count()
expect(sc).to_equal(0)
expect(ic).to_equal(0)
```

</details>

#### with_messages() pre-loads inbound queue

- var bt = BufferTransport with messages
   - Expected: ic equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.with_messages(["hello", "world"])
val ic = bt.inbound_count()
expect(ic).to_equal(2)
```

</details>

#### with_messages() preserves order (index 0 first)

- var bt = BufferTransport with messages
   - Expected: msg equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.with_messages(["first", "second"])
val msg = bt.read_message() ?? ""
expect(msg).to_equal("first")
```

</details>

### BufferTransport - read_message

#### returns exact message text

- var bt = BufferTransport with messages
   - Expected: msg equals `{"method":"ping"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.with_messages(["{\"method\":\"ping\"}"])
val msg = bt.read_message() ?? ""
expect(msg).to_equal("{\"method\":\"ping\"}")
```

</details>

#### returns nil when queue is empty

- var bt = BufferTransport new
   - Expected: got_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
val got_nil = bt.read_message() == nil
expect(got_nil).to_equal(true)
```

</details>

#### dequeues in FIFO order

- var bt = BufferTransport with messages
   - Expected: m1 equals `a`
   - Expected: m2 equals `b`
   - Expected: m3 equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.with_messages(["a", "b", "c"])
val m1 = bt.read_message() ?? ""
val m2 = bt.read_message() ?? ""
val m3 = bt.read_message() ?? ""
expect(m1).to_equal("a")
expect(m2).to_equal("b")
expect(m3).to_equal("c")
```

</details>

#### returns nil after all messages consumed

- var bt = BufferTransport with messages
- bt read message
   - Expected: got_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.with_messages(["only"])
bt.read_message()
val got_nil = bt.read_message() == nil
expect(got_nil).to_equal(true)
```

</details>

#### inbound_count decrements after each read

- var bt = BufferTransport with messages
- bt read message
   - Expected: ic equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.with_messages(["x", "y"])
bt.read_message()
val ic = bt.inbound_count()
expect(ic).to_equal(1)
```

</details>

### BufferTransport - write_message

#### captured message equals sent text

- var bt = BufferTransport new
- bt write message
   - Expected: sent.len() equals `1`
   - Expected: sent[0] equals `{"result":"ok"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
bt.write_message("{\"result\":\"ok\"}")
val sent = bt.all_sent()
expect(sent.len()).to_equal(1)
expect(sent[0]).to_equal("{\"result\":\"ok\"}")
```

</details>

#### sent_count increments

- var bt = BufferTransport new
- bt write message
- bt write message
   - Expected: sc equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
bt.write_message("msg1")
bt.write_message("msg2")
val sc = bt.sent_count()
expect(sc).to_equal(2)
```

</details>

#### all_sent preserves insertion order

- var bt = BufferTransport new
- bt write message
- bt write message
   - Expected: sent[0] equals `alpha`
   - Expected: sent[1] equals `beta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
bt.write_message("alpha")
bt.write_message("beta")
val sent = bt.all_sent()
expect(sent[0]).to_equal("alpha")
expect(sent[1]).to_equal("beta")
```

</details>

#### pop_sent removes oldest first

- var bt = BufferTransport new
- bt write message
- bt write message
   - Expected: p1 equals `first`
   - Expected: p2 equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
bt.write_message("first")
bt.write_message("second")
val p1 = bt.pop_sent() ?? ""
val p2 = bt.pop_sent() ?? ""
expect(p1).to_equal("first")
expect(p2).to_equal("second")
```

</details>

#### pop_sent returns nil when empty

- var bt = BufferTransport new
   - Expected: got_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
val got_nil = bt.pop_sent() == nil
expect(got_nil).to_equal(true)
```

</details>

### BufferTransport - push_inbound

#### appends to inbound queue

- var bt = BufferTransport new
- bt push inbound
   - Expected: ic equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
bt.push_inbound("dynamic")
val ic = bt.inbound_count()
expect(ic).to_equal(1)
```

</details>

#### reads pushed message

- var bt = BufferTransport new
- bt push inbound
   - Expected: msg equals `pushed_msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
bt.push_inbound("pushed_msg")
val msg = bt.read_message() ?? ""
expect(msg).to_equal("pushed_msg")
```

</details>

### BufferTransport - close

#### read_message returns nil after close

- var bt = BufferTransport with messages
- bt close
   - Expected: got_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.with_messages(["queued"])
bt.close()
val got_nil = bt.read_message() == nil
expect(got_nil).to_equal(true)
```

</details>

#### write_message is a no-op after close

- var bt = BufferTransport new
- bt close
- bt write message
   - Expected: sc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
bt.close()
bt.write_message("ignored")
val sc = bt.sent_count()
expect(sc).to_equal(0)
```

</details>

### Transport trait-object dispatch

#### transport_send routes to BufferTransport.write_message

- var bt = BufferTransport new
- transport send
   - Expected: sent.len() equals `1`
   - Expected: sent[0] equals `dispatched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
transport_send(bt, "dispatched")
val sent = bt.all_sent()
expect(sent.len()).to_equal(1)
expect(sent[0]).to_equal("dispatched")
```

</details>

#### transport_send works with multiple messages

- var bt = BufferTransport new
- transport send
- transport send
   - Expected: sc equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bt = BufferTransport.new()
transport_send(bt, "msg_a")
transport_send(bt, "msg_b")
val sc = bt.sent_count()
expect(sc).to_equal(2)
```

</details>

### StdioTransport - construction

#### new() constructs without error

- var st = StdioTransport new
   - Expected: closed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = StdioTransport.new()
val closed = st.closed
expect(closed).to_equal(false)
```

</details>

#### json_lines() constructs without error

- var st = StdioTransport json lines
   - Expected: closed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = StdioTransport.json_lines()
val closed = st.closed
expect(closed).to_equal(false)
```

</details>

#### write_message does not crash on a simple payload

- var st = StdioTransport json lines
- st write message
   - Expected: closed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# write_message calls write_stdout_message which calls print_raw.
# We verify success by checking closed is still false after the call.
var st = StdioTransport.json_lines()
st.write_message("{\"jsonrpc\":\"2.0\",\"method\":\"ping\"}")
val closed = st.closed
expect(closed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mcp_sdk/transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BufferTransport - construction
- BufferTransport - read_message
- BufferTransport - write_message
- BufferTransport - push_inbound
- BufferTransport - close
- Transport trait-object dispatch
- StdioTransport - construction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

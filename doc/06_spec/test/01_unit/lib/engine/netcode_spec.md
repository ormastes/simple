# Netcode Specification

> 1. var srv = GameServer new

<!-- sdn-diagram:id=netcode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=netcode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

netcode_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=netcode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Netcode Specification

## Scenarios

### GameServer

#### connects clients and tracks count

1. var srv = GameServer new
2. srv start
   - Expected: srv.client_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var srv = GameServer.new(4, 60)
srv.start()
val c1 = srv.connect_client("10.0.0.1")
val c2 = srv.connect_client("10.0.0.2")
expect(c1).to_be_greater_than(0)
expect(c2).to_be_greater_than(0)
expect(srv.client_count()).to_equal(2)
```

</details>

#### rejects clients when full

1. var srv = GameServer new
2. srv start
   - Expected: c2 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var srv = GameServer.new(1, 60)
srv.start()
val c1 = srv.connect_client("10.0.0.1")
val c2 = srv.connect_client("10.0.0.2")
expect(c1).to_be_greater_than(0)
expect(c2).to_equal(-1)
```

</details>

#### disconnects client

1. var srv = GameServer new
2. srv start
   - Expected: srv.client_count() equals `1`
3. srv disconnect client
   - Expected: srv.client_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var srv = GameServer.new(4, 60)
srv.start()
val cid = srv.connect_client("10.0.0.1")
expect(srv.client_count()).to_equal(1)
srv.disconnect_client(cid)
expect(srv.client_count()).to_equal(0)
```

</details>

#### advances tick

1. var srv = GameServer new
2. srv start
3. srv tick
4. srv tick
5. srv tick
   - Expected: srv.get_tick() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var srv = GameServer.new(4, 60)
srv.start()
srv.tick()
srv.tick()
srv.tick()
expect(srv.get_tick()).to_equal(3)
```

</details>

### GameClient

#### connects and tracks state

1. var cl = GameClient new
   - Expected: cl.is_connected() is false
2. cl connect
   - Expected: cl.is_connected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cl = GameClient.new("127.0.0.1")
expect(cl.is_connected()).to_equal(false)
cl.connect(42)
expect(cl.is_connected()).to_equal(true)
```

</details>

#### buffers input commands

1. var cl = GameClient new
2. cl connect
3. cl send input
4. cl send input
   - Expected: cl.input_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cl = GameClient.new("127.0.0.1")
cl.connect(1)
cl.send_input(1.0, 0.0, 0.0)
cl.send_input(0.0, 1.0, 0.0)
expect(cl.input_count()).to_equal(2)
```

</details>

#### receives server state snapshots

1. var cl = GameClient new
2. cl connect
3. cl receive state
   - Expected: cl.state_count() equals `1`
   - Expected: cl.get_server_tick() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cl = GameClient.new("127.0.0.1")
cl.connect(1)
cl.receive_state(10, 5.0, 0.0, 3.0, 1.0, 0.0, 0.0)
expect(cl.state_count()).to_equal(1)
expect(cl.get_server_tick()).to_equal(10)
```

</details>

### StateSync

#### registers entities and sets fields

1. var ss = StateSync new
2. ss register entity
3. ss set field
   - Expected: ss.entity_count() equals `1`
   - Expected: ss.get_field_value(1, "hp") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ss = StateSync.new(10)
ss.register_entity(1, 0)
ss.set_field(1, "hp", "100")
expect(ss.entity_count()).to_equal(1)
expect(ss.get_field_value(1, "hp")).to_equal("100")
```

</details>

#### tracks dirty fields

1. var ss = StateSync new
2. ss register entity
3. ss set field
4. ss set field
   - Expected: ss.get_dirty_count(1) equals `2`
5. ss mark synced
   - Expected: ss.get_dirty_count(1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ss = StateSync.new(10)
ss.register_entity(1, 0)
ss.set_field(1, "hp", "100")
ss.set_field(1, "mana", "50")
expect(ss.get_dirty_count(1)).to_equal(2)
ss.mark_synced(1)
expect(ss.get_dirty_count(1)).to_equal(0)
```

</details>

### RPCDispatcher

#### registers and dispatches calls

1. var rpc = RPCDispatcher new
2. rpc register
3. rpc register
   - Expected: rpc.registration_count() equals `2`
4. args push
   - Expected: ok is true
   - Expected: rpc.call_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpc = RPCDispatcher.new(100)
rpc.register("fire", "server", true)
rpc.register("jump", "client", false)
expect(rpc.registration_count()).to_equal(2)
var args: [text] = []
args.push("weapon1")
val ok = rpc.dispatch("fire", 1, args, 0.016)
expect(ok).to_equal(true)
expect(rpc.call_count()).to_equal(1)
```

</details>

#### rejects unregistered method

1. var rpc = RPCDispatcher new
   - Expected: ok is false
   - Expected: rpc.call_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpc = RPCDispatcher.new(100)
var args: [text] = []
val ok = rpc.dispatch("nonexistent", 1, args, 0.0)
expect(ok).to_equal(false)
expect(rpc.call_count()).to_equal(0)
```

</details>

#### unregisters methods

1. var rpc = RPCDispatcher new
2. rpc register
   - Expected: rpc.is_registered("fire") is true
3. rpc unregister
   - Expected: rpc.is_registered("fire") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpc = RPCDispatcher.new(100)
rpc.register("fire", "server", true)
expect(rpc.is_registered("fire")).to_equal(true)
rpc.unregister("fire")
expect(rpc.is_registered("fire")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/netcode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GameServer
- GameClient
- StateSync
- RPCDispatcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

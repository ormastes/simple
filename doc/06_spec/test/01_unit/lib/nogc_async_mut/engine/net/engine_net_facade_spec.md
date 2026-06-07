# Engine Net Facade Specification

> 1. var server = GameServer new

<!-- sdn-diagram:id=engine_net_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_net_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_net_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_net_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Net Facade Specification

## Scenarios

### nogc_async_mut engine net facade

#### re-exports server, client, sync, and rpc behavior

1. var server = GameServer new
2. server start
   - Expected: client_id equals `1`
   - Expected: server.client_count() equals `1`
3. server tick
   - Expected: server.get_tick() equals `1`
4. var client = GameClient new
5. client connect
6. client send input
   - Expected: client.is_connected() is true
   - Expected: client.input_count() equals `1`
7. client receive state
   - Expected: client.get_server_tick() equals `3`
   - Expected: client.state_count() equals `1`
8. var state sync = StateSync new
   - Expected: state_sync.register_entity(7, client_id) is true
9. state sync set field
   - Expected: state_sync.entity_count() equals `1`
   - Expected: state_sync.get_dirty_count(7) equals `1`
   - Expected: state_sync.get_field_value(7, "x") equals `10`
10. state sync tick
11. state sync mark synced
   - Expected: state_sync.get_dirty_count(7) equals `0`
12. var rpc = RPCDispatcher new
   - Expected: rpc.register("move", "player", true) is true
   - Expected: rpc.is_registered("move") is true
   - Expected: rpc.dispatch("move", client_id, ["left"], 1.0) is true
   - Expected: rpc.call_count() equals `1`
   - Expected: rpc.unregister("move") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var server = GameServer.new(2, 60)
server.start()
val client_id = server.connect_client("127.0.0.1:9000")
expect(client_id).to_equal(1)
expect(server.client_count()).to_equal(1)
server.tick()
expect(server.get_tick()).to_equal(1)

var client = GameClient.new("127.0.0.1:9000")
client.connect(client_id)
client.send_input(1.0, 0.0, 0.0)
expect(client.is_connected()).to_equal(true)
expect(client.input_count()).to_equal(1)
client.receive_state(3, 10.0, 2.0, 0.0, 0.1, 0.0, 0.0)
expect(client.get_server_tick()).to_equal(3)
expect(client.state_count()).to_equal(1)

var state_sync = StateSync.new(2)
expect(state_sync.register_entity(7, client_id)).to_equal(true)
state_sync.set_field(7, "x", "10")
expect(state_sync.entity_count()).to_equal(1)
expect(state_sync.get_dirty_count(7)).to_equal(1)
expect(state_sync.get_field_value(7, "x")).to_equal("10")
state_sync.tick()
state_sync.mark_synced(7)
expect(state_sync.get_dirty_count(7)).to_equal(0)

var rpc = RPCDispatcher.new(4)
expect(rpc.register("move", "player", true)).to_equal(true)
expect(rpc.is_registered("move")).to_equal(true)
expect(rpc.dispatch("move", client_id, ["left"], 1.0)).to_equal(true)
expect(rpc.call_count()).to_equal(1)
expect(rpc.unregister("move")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/net/engine_net_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut engine net facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

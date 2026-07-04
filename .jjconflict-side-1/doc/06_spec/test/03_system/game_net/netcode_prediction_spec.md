# Netcode: prediction, reconciliation & transactions

> Deterministic virtual-clock + loopback vertical slice for the netcode prediction plan. Every oracle below is an absolute value (exact positions, byte-identity, world hash) because the demo sim (`game_net/demo_sim.spl`) is a pure fixed-step integrator: the same `(state, input, dt)` always produces the same `SimState`.

<!-- sdn-diagram:id=netcode_prediction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=netcode_prediction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

netcode_prediction_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=netcode_prediction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Netcode: prediction, reconciliation & transactions

Deterministic virtual-clock + loopback vertical slice for the netcode prediction plan. Every oracle below is an absolute value (exact positions, byte-identity, world hash) because the demo sim (`game_net/demo_sim.spl`) is a pure fixed-step integrator: the same `(state, input, dt)` always produces the same `SimState`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_engine/netcode_prediction_plan.md |
| Design | N/A |
| Research | doc/01_research/app/game_engine/netcode_prediction.md |
| Source | `test/03_system/game_net/netcode_prediction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Deterministic virtual-clock + loopback vertical slice for the netcode
prediction plan. Every oracle below is an absolute value (exact positions,
byte-identity, world hash) because the demo sim (`game_net/demo_sim.spl`) is
a pure fixed-step integrator: the same `(state, input, dt)` always produces
the same `SimState`.

Fixed step: `dt = 0.1`, `SPEED = 5.0` → a full `move_x = 1.0` input advances
`pos_x` by exactly `0.5` per tick (an exact f32 value), so replay/reconcile
convergence can be asserted with plain `==`, not an epsilon.

## Examples

```simple
var predictor = Predictor.new(entity_id)
predictor.apply_input(move_x, move_y, dt)      # predict immediately
reconcile(predictor, authoritative_snapshot, dt)  # rewind + replay unacked
```

## Scenarios

### Netcode: client prediction + server reconciliation

#### client predicts N steps ahead of last server tick

- var predictor = Predictor new
- predictor apply input
   - Expected: predictor.local_tick equals `5u32`
   - Expected: predictor.server_tick equals `0u32`
   - Expected: predictor.prediction_ahead() equals `5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var predictor = Predictor.new(1u32)
var i = 0
while i < 5:
    predictor.apply_input(1.0, 0.0, DT)
    i = i + 1
# local_tick == server_tick + N (exact): no snapshot has arrived yet.
expect(predictor.local_tick).to_equal(5u32)
expect(predictor.server_tick).to_equal(0u32)
expect(predictor.prediction_ahead()).to_equal(5u32)
```

</details>

#### server correction converges to server state within K steps

- var predictor = Predictor new
- predictor apply input
   - Expected: predictor.state.pos_x equals `2.5)   # 5 ticks * 0.5`
- var server state = sim state new
- server state = sim step
- server state = sim step
- server state = sim step
   - Expected: server_state.pos_x equals `1.5)      # 3 ticks * 0.5`
   - Expected: applied is true
   - Expected: predictor.server_tick equals `3u32`
   - Expected: unacked_before - predictor.inputs.len() equals `3u64`
   - Expected: predictor.inputs.len() equals `2u64`
- var reference = sim state new
- reference = sim step
   - Expected: predictor.state.pos_x equals `reference.pos_x`
   - Expected: predictor.state.pos_x equals `2.5)   # |err| == 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var predictor = Predictor.new(1u32)
var i = 0
while i < 5:
    predictor.apply_input(1.0, 0.0, DT)
    i = i + 1
expect(predictor.state.pos_x).to_equal(2.5)   # 5 ticks * 0.5

# Server independently ran only the first 3 (of the same) inputs.
var server_state = sim_state_new(1u32)
server_state = sim_step(server_state, 1.0, 0.0, DT)
server_state = sim_step(server_state, 1.0, 0.0, DT)
server_state = sim_step(server_state, 1.0, 0.0, DT)
expect(server_state.pos_x).to_equal(1.5)      # 3 ticks * 0.5

val snap = Snapshot(tick: 3u32, ack_input_seq: 3u32, entities: [_entity_of(server_state)])
val unacked_before = predictor.inputs.len()
val applied = reconcile(predictor, snap, DT)
expect(applied).to_equal(true)
expect(predictor.server_tick).to_equal(3u32)
# K = the 2 buffered inputs (seq 4, 5) replayed on top of the rewind.
expect(unacked_before - predictor.inputs.len()).to_equal(3u64)
expect(predictor.inputs.len()).to_equal(2u64)

# Independent oracle: a from-scratch straight-line run of all 5
# inputs (no prediction/rewind machinery at all) must match exactly.
var reference = sim_state_new(1u32)
var j = 0
while j < 5:
    reference = sim_step(reference, 1.0, 0.0, DT)
    j = j + 1
expect(predictor.state.pos_x).to_equal(reference.pos_x)
expect(predictor.state.pos_x).to_equal(2.5)   # |err| == 0
```

</details>

#### un-corrected steady state stays byte-identical (no jitter)

- var a = Predictor new
- var b = Predictor new
- a apply input
- b apply input
   - Expected: bytes_a.len() equals `bytes_b.len()`
   - Expected: all_equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Predictor.new(7u32)
var b = Predictor.new(7u32)
var i = 0
while i < 4:
    a.apply_input(0.3, -0.6, DT)
    b.apply_input(0.3, -0.6, DT)
    i = i + 1
# No snapshot arrives for either ⇒ no reconcile call ⇒ two
# independently-run predictors given the same inputs stay
# byte-identical (the wire encoding is the identity oracle).
val bytes_a = encode_input_frame(InputFrame(seq: 1u32, tick: 1u32, move_x: a.state.pos_x, move_y: a.state.pos_y))
val bytes_b = encode_input_frame(InputFrame(seq: 1u32, tick: 1u32, move_x: b.state.pos_x, move_y: b.state.pos_y))
expect(bytes_a.len()).to_equal(bytes_b.len())
var k: u64 = 0
var all_equal = true
while k < bytes_a.len().to_u64():
    if bytes_a[k] != bytes_b[k]:
        all_equal = false
    k = k + 1
expect(all_equal).to_equal(true)
```

</details>

### Netcode: lossy channel recovery

#### dropped input frame recovered via next ack + replay

- var predictor = Predictor new
- var server = GameNetServer new
- clock advance
- channel send
- clock advance
- server fixed update
   - Expected: final_snap.ack_input_seq equals `5u32)   # seq 3 self-healed via resend`
- var baseline = sim state new
- baseline = sim step
   - Expected: final_snap.entities[0].pos_x equals `baseline.pos_x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clock = VirtualClock.new()
val channel = LoopbackChannel.new(42, 10u64, 0u64, 0u64)   # 10ms fixed latency, no jitter/loss knob used here
var predictor = Predictor.new(1u32)
var server = GameNetServer.new(DT)
val cid = server.connect(1u32)

# 5 client ticks; input #3's OWN packet (the tick-3 transmission) is
# dropped on the wire — a single transient loss (engineered here;
# the seeded loss knob is proven separately in the loopback unit
# spec). The client keeps resending its whole unacked backlog every
# tick (standard redundant-input recovery), so seq 3 rides along
# inside the seq-4 and seq-5 resends even though its own tick-3
# packet never arrived.
var tick = 0
var seq3_drop_done = false
while tick < 5:
    val frame = predictor.apply_input(1.0, 0.0, DT)
    clock.advance(1u64)
    var send_idx: u64 = 0
    val backlog = predictor.inputs.unacked()
    while send_idx < backlog.len().to_u64():
        val f = backlog[send_idx]
        if f.seq == 3u32 and not seq3_drop_done:
            seq3_drop_done = true   # drop only this one transmission
        else:
            channel.send(clock.now(), encode_input_frame(f))
        send_idx = send_idx + 1
    clock.advance(15u64)   # let the 10ms-latency backlog arrive
    val ready = channel.drain_ready(clock.now())
    var r: u64 = 0
    while r < ready.len().to_u64():
        match decode_input_frame(ready[r]):
            case Ok(f): server.submit_input(cid, f)
            case Err(_): assert_true(false)
        r = r + 1
    server.fixed_update()
    tick = tick + 1

val final_snap = server.snapshot_for(cid)
expect(final_snap.ack_input_seq).to_equal(5u32)   # seq 3 self-healed via resend

# Loss-free baseline: same 5 inputs, nothing ever dropped.
var baseline = sim_state_new(1u32)
var b = 0
while b < 5:
    baseline = sim_step(baseline, 1.0, 0.0, DT)
    b = b + 1
expect(final_snap.entities[0].pos_x).to_equal(baseline.pos_x)
```

</details>

#### reordered snapshots apply by tick, older ignored

- var predictor = Predictor new
- var newer state = sim state new
- newer state = sim step
- newer state = sim step
   - Expected: applied_newer is true
   - Expected: predictor.server_tick equals `8u32`
   - Expected: predictor.state.pos_x equals `1.0`
- var older state = sim state new
- older state = sim step
   - Expected: applied_older is false
   - Expected: predictor.server_tick equals `8u32)   # unchanged`
   - Expected: predictor.state.pos_x equals `1.0)    # unchanged: state == newest-tick state`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var predictor = Predictor.new(1u32)
var newer_state = sim_state_new(1u32)
newer_state = sim_step(newer_state, 1.0, 0.0, DT)
newer_state = sim_step(newer_state, 1.0, 0.0, DT)
val newer = Snapshot(tick: 8u32, ack_input_seq: 0u32, entities: [_entity_of(newer_state)])
val applied_newer = reconcile(predictor, newer, DT)
expect(applied_newer).to_equal(true)
expect(predictor.server_tick).to_equal(8u32)
expect(predictor.state.pos_x).to_equal(1.0)

var older_state = sim_state_new(1u32)
older_state = sim_step(older_state, -1.0, 0.0, DT)   # would move the wrong way if applied
val older = Snapshot(tick: 5u32, ack_input_seq: 0u32, entities: [_entity_of(older_state)])
val applied_older = reconcile(predictor, older, DT)
expect(applied_older).to_equal(false)          # stale tick, ignored
expect(predictor.server_tick).to_equal(8u32)   # unchanged
expect(predictor.state.pos_x).to_equal(1.0)    # unchanged: state == newest-tick state
```

</details>

### Netcode: transactional inventory op

#### accepted op commits authoritative state

- var client = TxnClient new
   - Expected: optimistic.gold equals `70`
   - Expected: validate_spend(wallet.gold, 30) is true
- client accept
   - Expected: optimistic.gold equals `server_wallet.gold`
   - Expected: client.pending_count() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = TxnClient.new()
val wallet = Wallet(gold: 100)
val result = client.begin_spend(wallet, 30)
val msg = result.msg
val optimistic = result.wallet
expect(optimistic.gold).to_equal(70)
expect(validate_spend(wallet.gold, 30)).to_equal(true)
client.accept(msg.op_seq)
# Server and client agree exactly: both settle on gold=70.
val server_wallet = Wallet(gold: wallet.gold - 30)
expect(optimistic.gold).to_equal(server_wallet.gold)
expect(client.pending_count()).to_equal(0u64)
```

</details>

#### rejected op rolls client back byte-identical to pre-op

- var client = TxnClient new
   - Expected: optimistic.gold equals `-10`
   - Expected: validate_spend(wallet.gold, 30) is false
   - Expected: restored_bytes.len() equals `pre_bytes.len()`
   - Expected: identical is true
   - Expected: w.gold equals `20`
- assert true
   - Expected: client.pending_count() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = TxnClient.new()
val wallet = Wallet(gold: 20)
val result = client.begin_spend(wallet, 30)   # optimistic spend, server will reject (insufficient funds)
val msg = result.msg
val optimistic = result.wallet
expect(optimistic.gold).to_equal(-10)
expect(validate_spend(wallet.gold, 30)).to_equal(false)
val pre_bytes = wallet_to_bytes(wallet)
val restored = client.reject(msg.op_seq)
if val w = restored:
    val restored_bytes = wallet_to_bytes(w)
    expect(restored_bytes.len()).to_equal(pre_bytes.len())
    var k: u64 = 0
    var identical = true
    while k < pre_bytes.len().to_u64():
        if pre_bytes[k] != restored_bytes[k]:
            identical = false
        k = k + 1
    expect(identical).to_equal(true)
    expect(w.gold).to_equal(20)
else:
    assert_true(false)
expect(client.pending_count()).to_equal(0u64)
```

</details>

#### cancel before ack restores pre-op snapshot

- var client = TxnClient new
   - Expected: identical is true
   - Expected: w.gold equals `50`
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = TxnClient.new()
val wallet = Wallet(gold: 50)
val result = client.begin_spend(wallet, 15)
val msg = result.msg
val pre_bytes = wallet_to_bytes(wallet)
val restored = client.cancel(msg.op_seq)
if val w = restored:
    val restored_bytes = wallet_to_bytes(w)
    var k: u64 = 0
    var identical = true
    while k < pre_bytes.len().to_u64():
        if pre_bytes[k] != restored_bytes[k]:
            identical = false
        k = k + 1
    expect(identical).to_equal(true)
    expect(w.gold).to_equal(50)
else:
    assert_true(false)
```

</details>

### Netcode: two-client convergence

#### two clients converge to identical world hash

- var server = GameNetServer new
- var predictor a = Predictor new
- var predictor b = Predictor new
- var interp a remote = Interpolator new
- var interp b remote = Interpolator new
- server submit input
- server submit input
- server fixed update
- reconcile
- reconcile
- interp a remote push snapshot
- interp b remote push snapshot
   - Expected: world_a[0].pos_x equals `world_b[0].pos_x`
   - Expected: world_a[0].pos_y equals `world_b[0].pos_y`
   - Expected: world_a[1].pos_x equals `world_b[1].pos_x`
   - Expected: world_a[1].pos_y equals `world_b[1].pos_y`
- hash a =
- hash b =
   - Expected: hash_a equals `hash_b`
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 84 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# One authoritative server, two owned entities (A=1, B=2). Both
# clients predict only their own entity and interpolate the other.
var server = GameNetServer.new(DT)
val cid_a = server.connect(1u32)
val cid_b = server.connect(2u32)
var predictor_a = Predictor.new(1u32)
var predictor_b = Predictor.new(2u32)
var interp_a_remote = Interpolator.new()   # client A's view of entity B
var interp_b_remote = Interpolator.new()   # client B's view of entity A

var tick = 0
while tick < 6:
    val frame_a = predictor_a.apply_input(1.0, 0.0, DT)
    val frame_b = predictor_b.apply_input(0.0, 1.0, DT)
    server.submit_input(cid_a, frame_a)
    server.submit_input(cid_b, frame_b)
    server.fixed_update()

    val snap_a = server.snapshot_for(cid_a)
    val snap_b = server.snapshot_for(cid_b)
    reconcile(predictor_a, snap_a, DT)
    reconcile(predictor_b, snap_b, DT)

    # Each client interpolates the entity it does not own, at t=1.0
    # (exact — matches the newest snapshot value, no smoothing lag).
    var j: u64 = 0
    while j < snap_a.entities.len().to_u64():
        val e = snap_a.entities[j]
        if e.entity_id == 2u32:
            interp_a_remote.push_snapshot(e)
        j = j + 1
    var m: u64 = 0
    while m < snap_b.entities.len().to_u64():
        val e = snap_b.entities[m]
        if e.entity_id == 1u32:
            interp_b_remote.push_snapshot(e)
        m = m + 1
    tick = tick + 1

val remote_b_via_a = interp_a_remote.lerp(1.0)
val remote_a_via_b = interp_b_remote.lerp(1.0)

if val rb = remote_b_via_a:
    if val ra = remote_a_via_b:
        # World A (client A's perspective): own entity (predicted/
        # reconciled) + remote entity (interpolated at t=1.0).
        val world_a: [EntityState] = [_entity_of(predictor_a.state), rb]
        # World B (client B's perspective): own entity + remote.
        val world_b: [EntityState] = [ra, _entity_of(predictor_b.state)]

        expect(world_a[0].pos_x).to_equal(world_b[0].pos_x)
        expect(world_a[0].pos_y).to_equal(world_b[0].pos_y)
        expect(world_a[1].pos_x).to_equal(world_b[1].pos_x)
        expect(world_a[1].pos_y).to_equal(world_b[1].pos_y)

        # Independently-computed world hash (FNV-1a over each
        # client's own serialization of its world view) must match.
        var hash_a: u32 = 2166136261u32
        var i: u64 = 0
        while i < 2:
            val e = world_a[i]
            val bytes = encode_input_frame(InputFrame(seq: 0u32, tick: 0u32, move_x: e.pos_x, move_y: e.pos_y))
            var bi: u64 = 0
            while bi < bytes.len().to_u64():
                hash_a = (hash_a ^ bytes[bi].to_u32()) * 16777619u32
                bi = bi + 1
            i = i + 1

        var hash_b: u32 = 2166136261u32
        i = 0
        while i < 2:
            val e = world_b[i]
            val bytes = encode_input_frame(InputFrame(seq: 0u32, tick: 0u32, move_x: e.pos_x, move_y: e.pos_y))
            var bi: u64 = 0
            while bi < bytes.len().to_u64():
                hash_b = (hash_b ^ bytes[bi].to_u32()) * 16777619u32
                bi = bi + 1
            i = i + 1

        expect(hash_a).to_equal(hash_b)
    else:
        assert_true(false)
else:
    assert_true(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/app/game_engine/netcode_prediction_plan.md](doc/03_plan/app/game_engine/netcode_prediction_plan.md)
- **Research:** [doc/01_research/app/game_engine/netcode_prediction.md](doc/01_research/app/game_engine/netcode_prediction.md)


</details>

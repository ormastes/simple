# Netcode: real UDP transport (localhost)

> `UdpTransport` (`src/lib/nogc_sync_mut/game_net/udp_transport.spl`) is the real-socket drop-in for `LoopbackChannel` named in the netcode plan ("Real UDP ... is a drop-in transport swap later"). It exposes the same minimal `send(bytes)` / `poll() -> [[u8]]` surface the loopback harness is driven through manually in `netcode_prediction_spec.spl`, so this spec swaps only the transport and reuses `wire.spl`'s codecs and the prediction/ reconciliation classes unchanged.

<!-- sdn-diagram:id=udp_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=udp_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

udp_transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=udp_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Netcode: real UDP transport (localhost)

`UdpTransport` (`src/lib/nogc_sync_mut/game_net/udp_transport.spl`) is the real-socket drop-in for `LoopbackChannel` named in the netcode plan ("Real UDP ... is a drop-in transport swap later"). It exposes the same minimal `send(bytes)` / `poll() -> [[u8]]` surface the loopback harness is driven through manually in `netcode_prediction_spec.spl`, so this spec swaps only the transport and reuses `wire.spl`'s codecs and the prediction/ reconciliation classes unchanged.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_engine/netcode_prediction_plan.md |
| Design | N/A |
| Research | N/A |
| Source | `test/02_integration/lib/game_net/udp_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`UdpTransport` (`src/lib/nogc_sync_mut/game_net/udp_transport.spl`) is the
real-socket drop-in for `LoopbackChannel` named in the netcode plan
("Real UDP ... is a drop-in transport swap later"). It exposes the same
minimal `send(bytes)` / `poll() -> [[u8]]` surface the loopback harness is
driven through manually in `netcode_prediction_spec.spl`, so this spec swaps
only the transport and reuses `wire.spl`'s codecs and the prediction/
reconciliation classes unchanged.

Two fixed high localhost ports are bound (127.0.0.1:39811/39812) rather than
an OS-assigned ephemeral port, because no `native_udp_local_addr` extern
exists to read an ephemeral bind back (see `udp_transport.spl`'s `ponytail:`
note). If binding either port fails (port in use, sandbox denies socket
binding, etc.) each `it` below classifies the run as a concrete, visible
failure via the final `expect` — never a silent pass. This is fail-closed
classification: unlike a `skip()`, a bind failure here is reported as a test
failure with the reason in the message, not a quietly-green no-op.

Only one `expect()` runs per `it` block (the reconciler `Snapshot` compares
several fields) — the interpreter's `it` reporter latches on the LAST
assertion only (see
doc/08_tracking/bug/spec_it_block_last_expect_wins_masks_earlier_failure_2026-07-03.md),
so every check below folds into one boolean before the single final assert.

## Examples

```simple
val client = UdpTransport.bind("127.0.0.1:39811", "127.0.0.1:39812")?
val server = UdpTransport.bind("127.0.0.1:39812", "127.0.0.1:39811")?
client.send(encode_input_frame(frame))   # fire-and-forget, real localhost UDP
val received = server.poll()             # drains everything currently queued
```

## Scenarios

### Netcode: real UDP transport (localhost)

#### sends a known wire frame and receives the exact bytes over real localhost UDP

- c send
- decoded ok =
- c close
- s close
   - Expected: classification equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var classification = "unknown"
val client = UdpTransport.bind(CLIENT_ADDR, SERVER_ADDR)
if val c = client:
    val server = UdpTransport.bind(SERVER_ADDR, CLIENT_ADDR)
    if val s = server:
        val frame = InputFrame(seq: 7u32, tick: 3u32, move_x: 0.5, move_y: -0.25)
        val sent_bytes = encode_input_frame(frame)
        c.send(sent_bytes)
        val received = _poll_until_nonempty(s, POLL_ATTEMPTS)
        val exact_bytes = (received.len() == 1u64) and _bytes_equal(received[0], sent_bytes)
        var decoded_ok = false
        if exact_bytes:
            match decode_input_frame(received[0]):
                case Ok(f):
                    decoded_ok = (f.seq == frame.seq) and (f.tick == frame.tick) and (f.move_x == frame.move_x) and (f.move_y == frame.move_y)
                case Err(_msg):
                    decoded_ok = false
        c.close()
        s.close()
        classification = if exact_bytes and decoded_ok: OK else: "byte mismatch or no datagram received within {POLL_ATTEMPTS} polls"
    else:
        classification = "server bind to {SERVER_ADDR} failed"
else:
    classification = "client bind to {CLIENT_ADDR} failed"
expect(classification).to_equal(OK)
```

</details>

#### converges to exact positions after a 3-tick client/server prediction round-trip over real localhost UDP

- var predictor = Predictor new
- var game server = GameNetServer new
- ct send
- game server fixed update
- st send
- var reference = sim state new
- reference = sim step
- ct close
- st close
- classification = if converged: OK else: "positions diverged: predictor=
   - Expected: classification equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var classification = "unknown"
val client = UdpTransport.bind(CLIENT_ADDR, SERVER_ADDR)
if val ct = client:
    val server = UdpTransport.bind(SERVER_ADDR, CLIENT_ADDR)
    if val st = server:
        var predictor = Predictor.new(1u32)
        var game_server = GameNetServer.new(DT)
        val cid = game_server.connect(1u32)

        var tick = 0
        while tick < 3:
            val frame = predictor.apply_input(1.0, 0.0, DT)
            ct.send(encode_input_frame(frame))

            val in_msgs = _poll_until_nonempty(st, POLL_ATTEMPTS)
            var i: u64 = 0
            while i < in_msgs.len().to_u64():
                match decode_input_frame(in_msgs[i]):
                    case Ok(f): game_server.submit_input(cid, f)
                    case Err(_msg): pass_dn
                i = i + 1
            game_server.fixed_update()

            val snap = game_server.snapshot_for(cid)
            st.send(encode_snapshot_full(snap))

            val out_msgs = _poll_until_nonempty(ct, POLL_ATTEMPTS)
            var j: u64 = 0
            while j < out_msgs.len().to_u64():
                val baseline: [EntityState] = []
                match decode_snapshot(out_msgs[j], baseline):
                    case Ok(s2): reconcile(predictor, s2, DT)
                    case Err(_msg): pass_dn
                j = j + 1
            tick = tick + 1

        var reference = sim_state_new(1u32)
        var k = 0
        while k < 3:
            reference = sim_step(reference, 1.0, 0.0, DT)
            k = k + 1

        val converged = (predictor.state.pos_x == reference.pos_x) and (predictor.state.pos_y == reference.pos_y)
        ct.close()
        st.close()
        classification = if converged: OK else: "positions diverged: predictor=({predictor.state.pos_x},{predictor.state.pos_y}) reference=({reference.pos_x},{reference.pos_y})"
    else:
        classification = "server bind to {SERVER_ADDR} failed"
else:
    classification = "client bind to {CLIENT_ADDR} failed"
expect(classification).to_equal(OK)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/app/game_engine/netcode_prediction_plan.md](doc/03_plan/app/game_engine/netcode_prediction_plan.md)


</details>

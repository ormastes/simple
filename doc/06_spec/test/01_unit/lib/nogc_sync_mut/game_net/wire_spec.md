# game_net wire frame codecs (KAT)

> Exact-byte known-answer tests for InputFrame / Snapshot (full + delta) / TxnMsg / Ack per the netcode prediction plan's P1 wire protocol slice. Every frame is versioned (`proto_ver:u16` + `msg_kind:u8`) and round-trips through `ByteWriter`/`ByteReader` byte-identically.

<!-- sdn-diagram:id=wire_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wire_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wire_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wire_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# game_net wire frame codecs (KAT)

Exact-byte known-answer tests for InputFrame / Snapshot (full + delta) / TxnMsg / Ack per the netcode prediction plan's P1 wire protocol slice. Every frame is versioned (`proto_ver:u16` + `msg_kind:u8`) and round-trips through `ByteWriter`/`ByteReader` byte-identically.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_engine/netcode_prediction_plan.md |
| Design | N/A |
| Research | doc/01_research/app/game_engine/netcode_prediction.md |
| Source | `test/01_unit/lib/nogc_sync_mut/game_net/wire_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exact-byte known-answer tests for InputFrame / Snapshot (full + delta) /
TxnMsg / Ack per the netcode prediction plan's P1 wire protocol slice. Every
frame is versioned (`proto_ver:u16` + `msg_kind:u8`) and round-trips through
`ByteWriter`/`ByteReader` byte-identically.

## Examples

```simple
val f = InputFrame(seq: 7u32, tick: 42u32, move_x: 1.0, move_y: -0.5)
val bytes = encode_input_frame(f)
val g = decode_input_frame(bytes)   # g == f, byte-identical round trip
```

## Scenarios

### game_net wire frame codecs

#### InputFrame round-trips with exact byte layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = InputFrame(seq: 7u32, tick: 42u32, move_x: 1.0, move_y: -0.5)
val bytes = encode_input_frame(f)
# header(3) + seq(4) + tick(4) + move_x(4) + move_y(4) = 19 bytes
expect(bytes.len()).to_equal(19)
expect(bytes[0]).to_equal(0u8)
expect(bytes[1]).to_equal(1u8)
expect(bytes[2]).to_equal(0u8)   # MSG_INPUT
match decode_input_frame(bytes):
    case Ok(g):
        expect(g.seq).to_equal(7u32)
        expect(g.tick).to_equal(42u32)
        expect(g.move_x).to_equal(1.0)
        expect(g.move_y).to_equal(-0.5)
    case Err(_): assert_true(false)
```

</details>

#### Snapshot full mode round-trips two entities with exact byte layout

- EntityState
- EntityState
   - Expected: bytes.len() equals `58`
   - Expected: g.tick equals `10u32`
   - Expected: g.ack_input_seq equals `3u32`
   - Expected: g.entities.len() equals `2`
   - Expected: g.entities[0].pos_x equals `0.5`
   - Expected: g.entities[1].vel_y equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entities: [EntityState] = [
    EntityState(entity_id: 1u32, pos_x: 0.5, pos_y: 0.0, vel_x: 5.0, vel_y: 0.0),
    EntityState(entity_id: 2u32, pos_x: 1.0, pos_y: 1.0, vel_x: 0.0, vel_y: 5.0)
]
val s = Snapshot(tick: 10u32, ack_input_seq: 3u32, entities: entities)
val bytes = encode_snapshot_full(s)
# header(3) + mode(1) + tick(4) + ack(4) + count(2) + 2*(id(4)+4*f32(16)) = 18 + 40 = 58
expect(bytes.len()).to_equal(58)
match decode_snapshot(bytes, []):
    case Ok(g):
        expect(g.tick).to_equal(10u32)
        expect(g.ack_input_seq).to_equal(3u32)
        expect(g.entities.len()).to_equal(2)
        expect(g.entities[0].pos_x).to_equal(0.5)
        expect(g.entities[1].vel_y).to_equal(5.0)
    case Err(_): assert_true(false)
```

</details>

#### Snapshot delta mode writes only dirty fields vs baseline

- EntityState
- EntityState
   - Expected: bytes.len() equals `23`
   - Expected: g.entities[0].pos_x equals `0.5`
   - Expected: g.entities[0].vel_x equals `5.0)   # merged from baseline, not on wire`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline: [EntityState] = [
    EntityState(entity_id: 1u32, pos_x: 0.0, pos_y: 0.0, vel_x: 5.0, vel_y: 0.0)
]
val updated: [EntityState] = [
    EntityState(entity_id: 1u32, pos_x: 0.5, pos_y: 0.0, vel_x: 5.0, vel_y: 0.0)
]
val s = Snapshot(tick: 11u32, ack_input_seq: 4u32, entities: updated)
val bytes = encode_snapshot_delta(s, baseline)
# header(3) + mode(1) + tick(4) + ack(4) + count(2) + id(4) + mask(1) + pos_x(4) = 23
expect(bytes.len()).to_equal(23)
match decode_snapshot(bytes, baseline):
    case Ok(g):
        expect(g.entities[0].pos_x).to_equal(0.5)
        expect(g.entities[0].vel_x).to_equal(5.0)   # merged from baseline, not on wire
    case Err(_): assert_true(false)
```

</details>

#### TxnMsg round-trips with payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload: [u8] = [9u8, 8u8, 7u8]
val t = TxnMsg(op_seq: 5u32, kind: 0u8, payload: payload)
val bytes = encode_txn_msg(t)
# header(3) + op_seq(4) + kind(1) + payload_len(2) + payload(3) = 13
expect(bytes.len()).to_equal(13)
match decode_txn_msg(bytes):
    case Ok(g):
        expect(g.op_seq).to_equal(5u32)
        expect(g.kind).to_equal(0u8)
        expect(g.payload.len()).to_equal(3)
        expect(g.payload[1]).to_equal(8u8)
    case Err(_): assert_true(false)
```

</details>

#### Ack round-trips with exact byte layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Ack(last_seq: 99u32)
val bytes = encode_ack(a)
expect(bytes.len()).to_equal(7)   # header(3) + last_seq(4)
match decode_ack(bytes):
    case Ok(g): expect(g.last_seq).to_equal(99u32)
    case Err(_): assert_true(false)
```

</details>

#### decode rejects a frame with the wrong msg_kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = InputFrame(seq: 1u32, tick: 1u32, move_x: 0.0, move_y: 0.0)
val bytes = encode_input_frame(f)
match decode_ack(bytes):
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_contain("expected MSG_ACK")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/app/game_engine/netcode_prediction_plan.md](doc/03_plan/app/game_engine/netcode_prediction_plan.md)
- **Research:** [doc/01_research/app/game_engine/netcode_prediction.md](doc/01_research/app/game_engine/netcode_prediction.md)


</details>

# game_net interest management (distance-based filtering)

> Minimal per-client interest management for the netcode plan's deferred interest-management slice: `interest_filter` keeps only entities within a client's view center + radius before a snapshot is encoded. Boundary rule: an entity exactly AT the radius is INSIDE the interest set (`dist <= radius`). Entering the interest set needs no wire change — the client's delta baseline simply won't have the entity yet, so `wire. encode_snapshot_delta` already forces full fields (same path as any never-before-seen entity). Leaving needs an explicit marker: `encode_snapshot_delta`'s `removed_ids` param writes `wire.DIRTY_REMOVE` for each, and `decode_snapshot` drops that entity instead of merging it from baseline.

<!-- sdn-diagram:id=interest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# game_net interest management (distance-based filtering)

Minimal per-client interest management for the netcode plan's deferred interest-management slice: `interest_filter` keeps only entities within a client's view center + radius before a snapshot is encoded. Boundary rule: an entity exactly AT the radius is INSIDE the interest set (`dist <= radius`). Entering the interest set needs no wire change — the client's delta baseline simply won't have the entity yet, so `wire. encode_snapshot_delta` already forces full fields (same path as any never-before-seen entity). Leaving needs an explicit marker: `encode_snapshot_delta`'s `removed_ids` param writes `wire.DIRTY_REMOVE` for each, and `decode_snapshot` drops that entity instead of merging it from baseline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_engine/netcode_prediction_plan.md |
| Design | N/A |
| Research | doc/01_research/app/game_engine/netcode_prediction.md |
| Source | `test/01_unit/lib/nogc_sync_mut/game_net/interest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Minimal per-client interest management for the netcode plan's deferred
interest-management slice: `interest_filter` keeps only entities within a
client's view center + radius before a snapshot is encoded. Boundary rule:
an entity exactly AT the radius is INSIDE the interest set (`dist <=
radius`). Entering the interest set needs no wire change — the client's
delta baseline simply won't have the entity yet, so `wire.
encode_snapshot_delta` already forces full fields (same path as any
never-before-seen entity). Leaving needs an explicit marker:
`encode_snapshot_delta`'s `removed_ids` param writes `wire.DIRTY_REMOVE` for
each, and `decode_snapshot` drops that entity instead of merging it from
baseline.

Every `it` below ends in exactly one `expect`/`assert` call (the interpreter
test runner has a live "last-expect-wins" bug where only the FINAL
expectation in a block gates pass/fail — see
`doc/08_tracking/bug/test_runner_interpreter_file_summary_greenwash_2026-07-03.md`),
so multi-fact checks are folded into one derived value before the single
final assertion.

## Examples

```simple
val visible = interest_filter(entities, view_x, view_y, radius)
val bytes = encode_snapshot_delta(snap, baseline, left_ids)   # left_ids -> DIRTY_REMOVE
```

## Scenarios

### interest_filter: distance boundary

#### inside, exactly-at, and one-epsilon-past the radius are filtered per the inclusive rule

- EntityState
- EntityState
- EntityState
   - Expected: mask equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eps: f32 = 0.001
val radius: f32 = 10.0
val entities: [EntityState] = [
    EntityState(entity_id: 1u32, pos_x: radius - eps, pos_y: 0.0, vel_x: 0.0, vel_y: 0.0),  # one epsilon inside
    EntityState(entity_id: 2u32, pos_x: radius, pos_y: 0.0, vel_x: 0.0, vel_y: 0.0),          # exactly at radius
    EntityState(entity_id: 3u32, pos_x: radius + eps, pos_y: 0.0, vel_x: 0.0, vel_y: 0.0)     # one epsilon outside
]
val filtered = interest_filter(entities, 0.0, 0.0, radius)
var mask = 0
if _has_id(filtered, 1u32):
    mask = mask + 1
if _has_id(filtered, 2u32):
    mask = mask + 2
if _has_id(filtered, 3u32):
    mask = mask + 4
# documented rule (dist <= radius is inside): id 1 and id 2 are
# kept, id 3 is dropped -> 1 + 2 + 0 = 3
expect(mask).to_equal(3)
```

</details>

### wire delta stream: enter/leave interest

#### an entering entity's delta frame is sized for a forced full field write (exact bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entering = EntityState(entity_id: 5u32, pos_x: 1.0, pos_y: 2.0, vel_x: 3.0, vel_y: 4.0)
val snap = Snapshot(tick: 1u32, ack_input_seq: 1u32, entities: [entering])
# baseline empty: this client has never seen id 5 before, so it is
# entering interest this tick with no prior state to diff against.
val bytes = encode_snapshot_delta(snap, [])
# header(3)+mode(1)+tick(4)+ack(4)+count(2)+id(4)+mask(1)+4*f32(16) = 35
expect(bytes.len()).to_equal(35)
```

</details>

#### an entering entity's full fields decode correctly with no prior baseline

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entering = EntityState(entity_id: 5u32, pos_x: 1.0, pos_y: 2.0, vel_x: 3.0, vel_y: 4.0)
val snap = Snapshot(tick: 1u32, ack_input_seq: 1u32, entities: [entering])
val bytes = encode_snapshot_delta(snap, [])
match decode_snapshot(bytes, []):
    case Ok(g):
        expect(g.entities[0].vel_y).to_equal(4.0)
    case Err(_):
        assert_true(false)
```

</details>

#### a leaving entity's removal frame is sized for an id+mask-only write (exact bytes)

- EntityState
   - Expected: bytes.len() equals `19`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline: [EntityState] = [
    EntityState(entity_id: 9u32, pos_x: 0.0, pos_y: 0.0, vel_x: 0.0, vel_y: 0.0)
]
val snap = Snapshot(tick: 2u32, ack_input_seq: 2u32, entities: [])
val bytes = encode_snapshot_delta(snap, baseline, [9u32])
# header(3)+mode(1)+tick(4)+ack(4)+count(2)+id(4)+mask(1) = 19, no field payload
expect(bytes.len()).to_equal(19)
```

</details>

#### the client drops a removed entity instead of merging it from baseline

- EntityState
   - Expected: g.entities.len() equals `0`
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline: [EntityState] = [
    EntityState(entity_id: 9u32, pos_x: 0.0, pos_y: 0.0, vel_x: 0.0, vel_y: 0.0)
]
val snap = Snapshot(tick: 2u32, ack_input_seq: 2u32, entities: [])
val bytes = encode_snapshot_delta(snap, baseline, [9u32])
match decode_snapshot(bytes, baseline):
    case Ok(g):
        expect(g.entities.len()).to_equal(0)
    case Err(_):
        assert_true(false)
```

</details>

### GameNetServer.snapshot_for: per-client interest wiring

#### nil interest config (default) stays broadcast-all, unchanged

- var server = GameNetServer new
- server connect
   - Expected: snap.entities.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var server = GameNetServer.new(0.1)
val cid1 = server.connect(1u32)
server.connect(2u32)
val snap = server.snapshot_for(cid1)
expect(snap.entities.len()).to_equal(2)
```

</details>

#### an explicit interest config filters the snapshot to what's in view

- var server = GameNetServer new
- server set interest
- server submit input
- server fixed update
- sig = snap entities len
   - Expected: sig equals `101u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var server = GameNetServer.new(0.1)
val cid1 = server.connect(1u32)   # stays at origin: no input submitted
val cid2 = server.connect(2u32)
server.set_interest(cid1, InterestConfig(center_x: 0.0, center_y: 0.0, radius: 5.0))
# Drive entity 2 out past the radius: SPEED=5.0, dt=0.1 -> 0.5/tick;
# 11 ticks -> pos_x = 5.5, which is past radius 5.0.
var tick = 0
while tick < 11:
    server.submit_input(cid2, InputFrame(seq: (tick + 1).to_u32(), tick: (tick + 1).to_u32(), move_x: 1.0, move_y: 0.0))
    server.fixed_update()
    tick = tick + 1
val snap = server.snapshot_for(cid1)
var sig: u32 = 0u32
if snap.entities.len() > 0:
    sig = snap.entities.len().to_u32() * 100u32 + snap.entities[0].entity_id
# exactly one visible entity (id 1, still at origin); id 2 is out of view
expect(sig).to_equal(101u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/app/game_engine/netcode_prediction_plan.md](doc/03_plan/app/game_engine/netcode_prediction_plan.md)
- **Research:** [doc/01_research/app/game_engine/netcode_prediction.md](doc/01_research/app/game_engine/netcode_prediction.md)


</details>

# game_net deterministic loopback + virtual clock

> Netcode plan P4: no OS sockets, no wall-clock reads. Seeded latency/jitter/ loss must be reproducible byte-for-byte given the same seed, and delivery is gated purely by the virtual clock.

<!-- sdn-diagram:id=loopback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loopback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loopback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loopback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# game_net deterministic loopback + virtual clock

Netcode plan P4: no OS sockets, no wall-clock reads. Seeded latency/jitter/ loss must be reproducible byte-for-byte given the same seed, and delivery is gated purely by the virtual clock.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_engine/netcode_prediction_plan.md |
| Design | N/A |
| Research | doc/01_research/app/game_engine/netcode_prediction.md |
| Source | `test/01_unit/lib/nogc_sync_mut/game_net/loopback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Netcode plan P4: no OS sockets, no wall-clock reads. Seeded latency/jitter/
loss must be reproducible byte-for-byte given the same seed, and delivery is
gated purely by the virtual clock.

## Examples

```simple
val channel = LoopbackChannel.new(seed, latency_ms, jitter_ms, loss_rate_pct)
channel.send(clock.now(), bytes)
val delivered = channel.drain_ready(clock.now())   # ready-at-or-before-now
```

## Scenarios

### game_net loopback channel

#### delivers nothing before the scheduled tick, then delivers exactly once

- var channel = LoopbackChannel new
- channel send
   - Expected: early.len() equals `0`
   - Expected: on_time.len() equals `1`
   - Expected: on_time[0][0] equals `42u8`
   - Expected: again.len() equals `0)   # already delivered, not re-delivered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var channel = LoopbackChannel.new(1, 10u64, 0u64, 0u64)
channel.send(0u64, [42u8])
val early = channel.drain_ready(5u64)
expect(early.len()).to_equal(0)
val on_time = channel.drain_ready(10u64)
expect(on_time.len()).to_equal(1)
expect(on_time[0][0]).to_equal(42u8)
val again = channel.drain_ready(20u64)
expect(again.len()).to_equal(0)   # already delivered, not re-delivered
```

</details>

#### same seed produces the same loss pattern and delivered count

- var c1 = LoopbackChannel new
- var c2 = LoopbackChannel new
- c1 send
- c2 send
   - Expected: r1.len() equals `r2.len()`
   - Expected: identical is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c1 = LoopbackChannel.new(7, 5u64, 3u64, 40u64)
var c2 = LoopbackChannel.new(7, 5u64, 3u64, 40u64)
var i = 0
while i < 20:
    c1.send(0u64, [i.to_u8()])
    c2.send(0u64, [i.to_u8()])
    i = i + 1
val r1 = c1.drain_ready(100u64)
val r2 = c2.drain_ready(100u64)
expect(r1.len()).to_equal(r2.len())
var k: u64 = 0
var identical = true
while k < r1.len().to_u64():
    if r1[k][0] != r2[k][0]:
        identical = false
    k = k + 1
expect(identical).to_equal(true)
```

</details>

#### 0% loss delivers every message eventually

- var channel = LoopbackChannel new
- channel send
   - Expected: delivered.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var channel = LoopbackChannel.new(3, 2u64, 5u64, 0u64)
var i = 0
while i < 10:
    channel.send(0u64, [i.to_u8()])
    i = i + 1
val delivered = channel.drain_ready(1000u64)
expect(delivered.len()).to_equal(10)
```

</details>

#### 100% loss delivers nothing

- var channel = LoopbackChannel new
- channel send
   - Expected: delivered.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var channel = LoopbackChannel.new(9, 2u64, 0u64, 100u64)
var i = 0
while i < 10:
    channel.send(0u64, [i.to_u8()])
    i = i + 1
val delivered = channel.drain_ready(1000u64)
expect(delivered.len()).to_equal(0)
```

</details>

### game_net virtual clock

#### advances deterministically with no wall-clock dependency

- var clock = VirtualClock new
   - Expected: clock.now() equals `0u64`
- clock advance
- clock advance
   - Expected: clock.now() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clock = VirtualClock.new()
expect(clock.now()).to_equal(0u64)
clock.advance(16u64)
clock.advance(16u64)
expect(clock.now()).to_equal(32u64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/app/game_engine/netcode_prediction_plan.md](doc/03_plan/app/game_engine/netcode_prediction_plan.md)
- **Research:** [doc/01_research/app/game_engine/netcode_prediction.md](doc/01_research/app/game_engine/netcode_prediction.md)


</details>

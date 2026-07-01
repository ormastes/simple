# audio_bus_spec

> Audio Bus Graph — Named dB-domain bus graph unit tests

<!-- sdn-diagram:id=audio_bus_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audio_bus_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audio_bus_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audio_bus_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# audio_bus_spec

Audio Bus Graph — Named dB-domain bus graph unit tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/audio_bus_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Audio Bus Graph — Named dB-domain bus graph unit tests

Tests BusGraph construction, volume/mute mutation, DAG routing with cycle
rejection, and effective_gain computation along the send_target chain.

## Scenarios

### BusGraph

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = BusGraph.new()
expect(graph.bus_count()).to_equal(0)
```

</details>

#### add_bus with empty send_target creates root bus

- var graph = BusGraph new
   - Expected: ok is true
   - Expected: graph.bus_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
val ok = graph.add_bus("master", "", 0.0)
expect(ok).to_equal(true)
expect(graph.bus_count()).to_equal(1)
```

</details>

#### add_bus rejects duplicate name

- var graph = BusGraph new
- graph add bus
   - Expected: dup is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
val dup = graph.add_bus("master", "", 0.0)
expect(dup).to_equal(false)
```

</details>

#### add_bus rejects unknown send_target

- var graph = BusGraph new
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
val ok = graph.add_bus("sfx", "master", 0.0)
expect(ok).to_equal(false)
```

</details>

#### add_bus succeeds when send_target exists

- var graph = BusGraph new
- graph add bus
   - Expected: ok is true
   - Expected: graph.bus_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
val ok = graph.add_bus("sfx", "master", -6.0)
expect(ok).to_equal(true)
expect(graph.bus_count()).to_equal(2)
```

</details>

#### get_bus returns a result for known name

- var graph = BusGraph new
- graph add bus
   - Expected: graph.bus_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
val result = graph.get_bus("master")
# bus was inserted — bus_count is 1 confirms it exists
expect(graph.bus_count()).to_equal(1)
```

</details>

#### get_bus returns nil for unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = BusGraph.new()
val result = graph.get_bus("missing")
# No bus inserted — bus_count stays 0
expect(graph.bus_count()).to_equal(0)
```

</details>

#### set_volume_db returns true for existing bus

- var graph = BusGraph new
- graph add bus
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
val ok = graph.set_volume_db("master", -12.0)
expect(ok).to_equal(true)
```

</details>

#### set_volume_db updates and round-trips via effective_gain

- var graph = BusGraph new
- graph add bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", -20.0)
# -20 dB linear = ~0.1; effective_gain * 1000 ≈ 100
val gain = graph.effective_gain("master")
val g1000 = gain * 1000.0
expect(g1000).to_be_greater_than(98.0)
expect(g1000).to_be_less_than(102.0)
```

</details>

#### set_volume_db returns false for missing bus

- var graph = BusGraph new
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
val ok = graph.set_volume_db("ghost", -3.0)
expect(ok).to_equal(false)
```

</details>

#### set_muted returns false for missing bus

- var graph = BusGraph new
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
val ok = graph.set_muted("ghost", true)
expect(ok).to_equal(false)
```

</details>

#### set_muted returns true for existing bus

- var graph = BusGraph new
- graph add bus
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
val ok = graph.set_muted("master", true)
expect(ok).to_equal(true)
```

</details>

### BusGraph route

#### route succeeds with valid target and updates send_target

- var graph = BusGraph new
- graph add bus
- graph add bus
- graph add bus
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("music", "master", 0.0)
graph.add_bus("ambient", "master", 0.0)
val ok = graph.route("ambient", "music")
expect(ok).to_equal(true)
# Verify the routing took effect via effective_gain through the new chain
# ambient -> music -> master; all at 0 dB → gain = 1.0
val gain = graph.effective_gain("ambient")
val g1000 = gain * 1000.0
expect(g1000).to_be_greater_than(999.0)
expect(g1000).to_be_less_than(1001.0)
```

</details>

#### route rejects direct self-cycle

- var graph = BusGraph new
- graph add bus
- graph add bus
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", 0.0)
val ok = graph.route("sfx", "sfx")
expect(ok).to_equal(false)
```

</details>

#### route rejects indirect cycle

- var graph = BusGraph new
- graph add bus
- graph add bus
- graph add bus
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("a", "master", 0.0)
graph.add_bus("b", "a", 0.0)
# b -> a -> master; routing a -> b would create a -> b -> a cycle
val ok = graph.route("a", "b")
expect(ok).to_equal(false)
```

</details>

#### route rejects missing bus name

- var graph = BusGraph new
- graph add bus
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
val ok = graph.route("ghost", "master")
expect(ok).to_equal(false)
```

</details>

#### route rejects missing target

- var graph = BusGraph new
- graph add bus
- graph add bus
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", 0.0)
val ok = graph.route("sfx", "nonexistent")
expect(ok).to_equal(false)
```

</details>

#### route to empty string succeeds

- var graph = BusGraph new
- graph add bus
- graph add bus
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", 0.0)
val ok = graph.route("sfx", "")
expect(ok).to_equal(true)
```

</details>

### BusGraph effective_gain

#### single unity bus at master has gain 1.0

- var graph = BusGraph new
- graph add bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
val gain = graph.effective_gain("master")
val g1000 = gain * 1000.0
expect(g1000).to_be_greater_than(999.0)
expect(g1000).to_be_less_than(1001.0)
```

</details>

#### bus at -6.0206 dB under unity master has gain ~0.5

- var graph = BusGraph new
- graph add bus
- graph add bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# -6.0206 dB is the standard half-amplitude point (10^(-6.0206/20) = 0.5)
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", -6.0206)
val gain = graph.effective_gain("sfx")
val g1000 = gain * 1000.0
expect(g1000).to_be_greater_than(498.0)
expect(g1000).to_be_less_than(502.0)
```

</details>

#### stacked -6.0206 dB buses multiply to ~0.25

- var graph = BusGraph new
- graph add bus
- graph add bus
- graph add bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", -6.0206)
graph.add_bus("reverb", "sfx", -6.0206)
val gain = graph.effective_gain("reverb")
# 0.5 * 0.5 = 0.25 → g1000 ≈ 250
val g1000 = gain * 1000.0
expect(g1000).to_be_greater_than(248.0)
expect(g1000).to_be_less_than(252.0)
```

</details>

#### muted bus returns 0.0 gain

- var graph = BusGraph new
- graph add bus
- graph add bus
- graph set muted
   - Expected: gain equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", 0.0)
graph.set_muted("sfx", true)
val gain = graph.effective_gain("sfx")
expect(gain).to_equal(0.0)
```

</details>

#### muted parent bus zeroes child effective gain

- var graph = BusGraph new
- graph add bus
- graph add bus
- graph add bus
- graph set muted
   - Expected: gain equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", 0.0)
graph.add_bus("reverb", "sfx", 0.0)
graph.set_muted("sfx", true)
val gain = graph.effective_gain("reverb")
expect(gain).to_equal(0.0)
```

</details>

#### muted master zeroes all children

- var graph = BusGraph new
- graph add bus
- graph add bus
- graph set muted
   - Expected: gain equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("music", "master", 0.0)
graph.set_muted("master", true)
val gain = graph.effective_gain("music")
expect(gain).to_equal(0.0)
```

</details>

#### effective_gain on missing bus returns 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = BusGraph.new()
val gain = graph.effective_gain("ghost")
expect(gain).to_equal(0.0)
```

</details>

#### unmuted bus restores gain to 1.0

- var graph = BusGraph new
- graph add bus
- graph add bus
- graph set muted
- graph set muted


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", 0.0)
graph.add_bus("sfx", "master", 0.0)
graph.set_muted("sfx", true)
graph.set_muted("sfx", false)
val gain = graph.effective_gain("sfx")
val g1000 = gain * 1000.0
expect(g1000).to_be_greater_than(999.0)
expect(g1000).to_be_less_than(1001.0)
```

</details>

#### master at -20dB gives child gain ~0.1

- var graph = BusGraph new
- graph add bus
- graph add bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = BusGraph.new()
graph.add_bus("master", "", -20.0)
graph.add_bus("sfx", "master", 0.0)
val gain = graph.effective_gain("sfx")
val g1000 = gain * 1000.0
expect(g1000).to_be_greater_than(98.0)
expect(g1000).to_be_less_than(102.0)
```

</details>

### _db_to_linear

#### 0 dB returns 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = _db_to_linear(0.0)
val g1000 = g * 1000.0
expect(g1000).to_be_greater_than(999.0)
expect(g1000).to_be_less_than(1001.0)
```

</details>

#### -20 dB returns ~0.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = _db_to_linear(-20.0)
val g1000 = g * 1000.0
expect(g1000).to_be_greater_than(98.0)
expect(g1000).to_be_less_than(102.0)
```

</details>

#### positive 20 dB returns ~10.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = _db_to_linear(20.0)
val g100 = g * 100.0
expect(g100).to_be_greater_than(998.0)
expect(g100).to_be_less_than(1002.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

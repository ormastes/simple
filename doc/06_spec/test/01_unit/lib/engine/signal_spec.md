# Signal Specification

> <details>

<!-- sdn-diagram:id=signal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=signal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

signal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=signal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Signal Specification

## Scenarios

### Signal

#### creates a signal with a name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = Signal(name: "on_hit", connections: [], next_id: 0, enabled: true)
expect(sig.name).to_equal("on_hit")
expect(sig.enabled).to_equal(true)
```

</details>

#### connects and emits to a listener

1. var sig = Signal
2. fn on data
3. sig emit
   - Expected: received equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var received = ""
var sig = Signal(name: "test", connections: [], next_id: 0, enabled: true)
fn on_data(data: text):
    received = data
val conn = sig.connect(on_data)
sig.emit("hello")
expect(received).to_equal("hello")
```

</details>

#### disconnects a listener

1. var sig = Signal
2. fn on inc
3. sig emit
   - Expected: count equals `1`
   - Expected: removed is true
4. sig emit
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
var sig = Signal(name: "test", connections: [], next_id: 0, enabled: true)
fn on_inc(data: text):
    count = count + 1
val conn = sig.connect(on_inc)
sig.emit("a")
expect(count).to_equal(1)
val removed = sig.disconnect(conn)
expect(removed).to_equal(true)
sig.emit("b")
expect(count).to_equal(1)
```

</details>

#### supports one-shot connections

1. var sig = Signal
2. fn on once
3. sig emit
4. sig emit
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
var sig = Signal(name: "test", connections: [], next_id: 0, enabled: true)
fn on_once(data: text):
    count = count + 1
val conn = sig.connect_once(on_once)
sig.emit("first")
sig.emit("second")
expect(count).to_equal(1)
```

</details>

#### emits to multiple listeners

1. var sig = Signal
2. fn on a
3. fn on b
4. sig emit
   - Expected: a_val equals `msg`
   - Expected: b_val equals `msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a_val = ""
var b_val = ""
var sig = Signal(name: "multi", connections: [], next_id: 0, enabled: true)
fn on_a(data: text):
    a_val = data
fn on_b(data: text):
    b_val = data
val ca = sig.connect(on_a)
val cb = sig.connect(on_b)
sig.emit("msg")
expect(a_val).to_equal("msg")
expect(b_val).to_equal("msg")
```

</details>

### EventBus

#### registers and emits named signals

1. var bus = EventBus
2. bus register
3. fn on damage
4. bus emit
   - Expected: result equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
var bus = EventBus(signals: {})
bus.register("damage")
fn on_damage(data: text):
    result = data
val conn = bus.connect("damage", on_damage)
bus.emit("damage", "50")
expect(result).to_equal("50")
```

</details>

#### auto-registers on connect

1. var bus = EventBus
2. fn on score
3. bus emit
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
var bus = EventBus(signals: {})
fn on_score(data: text):
    result = data
val conn = bus.connect("score", on_score)
bus.emit("score", "100")
expect(result).to_equal("100")
```

</details>

#### does not cross-emit between different signals

1. var bus = EventBus
2. fn on alpha
3. fn on beta
4. bus emit
   - Expected: a_result equals `aaa`
   - Expected: b_result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a_result = ""
var b_result = ""
var bus = EventBus(signals: {})
fn on_alpha(data: text):
    a_result = data
fn on_beta(data: text):
    b_result = data
val ca = bus.connect("alpha", on_alpha)
val cb = bus.connect("beta", on_beta)
bus.emit("alpha", "aaa")
expect(a_result).to_equal("aaa")
expect(b_result).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/signal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Signal
- EventBus

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

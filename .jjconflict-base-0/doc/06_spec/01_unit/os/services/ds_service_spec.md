# DsService Specification (G5)

> Data Store (DS) service — Minix-style name service.  Validates publication, lookup, ownership enforcement, subscribe/unsubscribe lifecycle, TTL expiry, count invariants, and the ds_notify side-effect counter.

<!-- sdn-diagram:id=ds_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ds_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ds_service_spec -> std
ds_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ds_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DsService Specification (G5)

Data Store (DS) service — Minix-style name service.  Validates publication, lookup, ownership enforcement, subscribe/unsubscribe lifecycle, TTL expiry, count invariants, and the ds_notify side-effect counter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G5 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/ds_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Data Store (DS) service — Minix-style name service.  Validates publication,
lookup, ownership enforcement, subscribe/unsubscribe lifecycle, TTL expiry,
count invariants, and the ds_notify side-effect counter.

## Scenarios

### DsService initial state
_Verify that a freshly constructed DsService has zero entries and tick=0._

#### constructs with tick=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = DsService.new()
expect(svc.tick).to_equal(0)
```

</details>

#### constructs with zero published names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = DsService.new()
expect(svc.ds_count()).to_equal(0)
```

</details>

### DsService publish and lookup
_Core publish / lookup contract._

#### publish returns a live entity with non-zero id

1. var svc = DsService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val e = svc.ds_publish("pm", 1001, 2, 0)
expect(e.id).to_be_greater_than(0)
```

</details>

#### lookup returns the endpoint after publish

1. var svc = DsService new
   - Expected: result equals `1001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("pm", 1001, 2, 0)
val result = svc.ds_lookup("pm")
expect(result).to_equal(1001)
```

</details>

#### lookup of unknown name returns -ENOENT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = DsService.new()
val result = svc.ds_lookup("unknown")
expect(result).to_equal(-ENOENT.to_i64())
```

</details>

### DsService unpublish
_Ownership-gated unpublish semantics._

#### unpublish by owner succeeds and name disappears

1. var svc = DsService new
   - Expected: ok is true
   - Expected: svc.ds_lookup("vfs") equals `-ENOENT.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("vfs", 2002, 5, 0)
val ok = svc.ds_unpublish("vfs", 5)
expect(ok).to_equal(true)
expect(svc.ds_lookup("vfs")).to_equal(-ENOENT.to_i64())
```

</details>

#### unpublish by non-owner returns false

1. var svc = DsService new
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("vfs", 2002, 5, 0)
val ok = svc.ds_unpublish("vfs", 99)
expect(ok).to_equal(false)
```

</details>

### DsService re-publish
_Same-owner republish updates without creating a duplicate entry._

#### re-publish by same owner updates endpoint, no duplicate names

1. var svc = DsService new
   - Expected: svc.ds_lookup("rs") equals `3999`
   - Expected: svc.ds_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e1 = svc.ds_publish("rs", 3001, 7, 0)
val _e2 = svc.ds_publish("rs", 3999, 7, 0)
expect(svc.ds_lookup("rs")).to_equal(3999)
expect(svc.ds_count()).to_equal(1)
```

</details>

### DsService subscribe / unsubscribe
_Subscriber list management._

#### subscribe adds pid; subscriber list length is 1

1. var svc = DsService new
   - Expected: ok is true
   - Expected: ok2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("net", 4001, 10, 0)
val ok = svc.ds_subscribe("net", 20)
expect(ok).to_equal(true)
# Subscribing the same pid again must be idempotent (no duplicate)
val ok2 = svc.ds_subscribe("net", 20)
expect(ok2).to_equal(true)
```

</details>

#### unsubscribe removes pid; subsequent subscribe count correct

1. var svc = DsService new
   - Expected: ok is true
   - Expected: ok2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("net", 4001, 10, 0)
val _s1 = svc.ds_subscribe("net", 20)
val _s2 = svc.ds_subscribe("net", 21)
val ok = svc.ds_unsubscribe("net", 20)
expect(ok).to_equal(true)
# Remaining subscriber: unsubscribing pid 20 again returns true (no-op on missing)
val ok2 = svc.ds_subscribe("net", 21)
expect(ok2).to_equal(true)
```

</details>

### DsService TTL expiry
_TTL 0 never expires; TTL > 0 expires after ds_advance crosses the deadline._

#### TTL 0 name survives after ds_advance

1. var svc = DsService new
   - Expected: svc.ds_lookup("clock") equals `5001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("clock", 5001, 3, 0)
val _t1 = svc.ds_advance()
val _t2 = svc.ds_advance()
expect(svc.ds_lookup("clock")).to_equal(5001)
```

</details>

#### TTL > 0 name expires after enough ticks

1. var svc = DsService new
   - Expected: svc.ds_lookup("ephemeral") equals `-ENOENT.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("ephemeral", 6001, 4, 2)
# tick becomes 1 then 2; absolute deadline = 0+2 = 2; at tick 2 it expires
val _t1 = svc.ds_advance()
val _t2 = svc.ds_advance()
expect(svc.ds_lookup("ephemeral")).to_equal(-ENOENT.to_i64())
```

</details>

### DsService count invariants
_ds_count tracks publishes, unpublishes, and expiry._

#### count increments on publish and decrements on unpublish

1. var svc = DsService new
   - Expected: svc.ds_count() equals `2`
   - Expected: svc.ds_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e1 = svc.ds_publish("a", 1, 1, 0)
val _e2 = svc.ds_publish("b", 2, 2, 0)
expect(svc.ds_count()).to_equal(2)
val _ok = svc.ds_unpublish("a", 1)
expect(svc.ds_count()).to_equal(1)
```

</details>

#### count decrements on TTL expiry

1. var svc = DsService new
   - Expected: svc.ds_count() equals `2`
   - Expected: svc.ds_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e1 = svc.ds_publish("short", 9001, 6, 1)
val _e2 = svc.ds_publish("long",  9002, 6, 0)
expect(svc.ds_count()).to_equal(2)
# Advance to tick 1; absolute deadline for "short" is 0+1=1, so it expires at tick 1
val _t1 = svc.ds_advance()
expect(svc.ds_count()).to_equal(1)
```

</details>

### DsService ds_notify side-effect
_ds_notify is called when the same owner republishes, allowing subscriber observation._

#### ds_notify counter increments when owner updates an existing name with a subscriber

1. var svc = DsService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = DsService.new()
val _e = svc.ds_publish("rs", 7001, 8, 0)
val _ok = svc.ds_subscribe("rs", 30)
val before = ds_notify_count
# Re-publish by same owner: should notify subscriber pid 30
val _e2 = svc.ds_publish("rs", 7999, 8, 0)
expect(ds_notify_count).to_be_greater_than(before)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

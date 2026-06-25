# Replay Baremetal Core Specification

> 1. bm replay set mode

<!-- sdn-diagram:id=replay_baremetal_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_baremetal_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_baremetal_core_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_baremetal_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Baremetal Core Specification

## Scenarios

### bm_replay mode

#### bm_replay default is off

1. bm replay set mode
   - Expected: bm_replay_is_off() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_replay_set_mode(0)
expect(bm_replay_is_off()).to_equal(true)
```

</details>

#### bm_replay set mode to record — is_off returns false

1. bm replay set mode
   - Expected: bm_replay_is_off() is false
2. bm replay set mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_replay_set_mode(1)
expect(bm_replay_is_off()).to_equal(false)
bm_replay_set_mode(0)
```

</details>

#### bm_replay set mode back to 0 — is_off returns true again

1. bm replay set mode
2. bm replay set mode
   - Expected: bm_replay_is_off() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_replay_set_mode(1)
bm_replay_set_mode(0)
expect(bm_replay_is_off()).to_equal(true)
```

</details>

#### bm_replay set mode to replay (2) — is_off returns false

1. bm replay set mode
   - Expected: bm_replay_is_off() is false
2. bm replay set mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_replay_set_mode(2)
expect(bm_replay_is_off()).to_equal(false)
bm_replay_set_mode(0)
```

</details>

### bm_ring init and count

#### bm_ring_init sets count to zero

1. bm ring init
   - Expected: bm_ring_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
expect(bm_ring_count()).to_equal(0)
```

</details>

#### bm_ring_count after init is 0

1. bm ring init
   - Expected: c equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
val c = bm_ring_count()
expect(c).to_equal(0)
```

</details>

### bm_ring push and count

#### push 1 event — count is 1

1. bm ring init
2. bm ring push
   - Expected: bm_ring_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(1, 100, 42, 99)
expect(bm_ring_count()).to_equal(1)
```

</details>

#### push 3 events — count is 3

1. bm ring init
2. bm ring push
3. bm ring push
4. bm ring push
   - Expected: bm_ring_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(1, 10, 1, 2)
bm_ring_push(2, 20, 3, 4)
bm_ring_push(3, 30, 5, 6)
expect(bm_ring_count()).to_equal(3)
```

</details>

### bm_ring push and pop

#### pop_kind returns pushed kind and decrements count

1. bm ring init
2. bm ring push
   - Expected: k equals `1`
   - Expected: bm_ring_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(1, 100, 42, 99)
val k = bm_ring_pop_kind()
expect(k).to_equal(1)
expect(bm_ring_count()).to_equal(0)
```

</details>

#### pop_timestamp returns pushed timestamp

1. bm ring init
2. bm ring push
   - Expected: ts equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(1, 100, 42, 99)
val ts = bm_ring_pop_timestamp()
expect(ts).to_equal(100)
```

</details>

#### pop_val_a returns pushed val_a

1. bm ring init
2. bm ring push
   - Expected: a equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(1, 100, 42, 99)
val a = bm_ring_pop_val_a()
expect(a).to_equal(42)
```

</details>

#### pop_val_b returns pushed val_b

1. bm ring init
2. bm ring push
   - Expected: b equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(1, 100, 42, 99)
val b = bm_ring_pop_val_b()
expect(b).to_equal(99)
```

</details>

#### pop_kind on empty ring returns 0

1. bm ring init
   - Expected: k equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
val k = bm_ring_pop_kind()
expect(k).to_equal(0)
```

</details>

#### pop_timestamp on empty ring returns 0

1. bm ring init
   - Expected: ts equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
val ts = bm_ring_pop_timestamp()
expect(ts).to_equal(0)
```

</details>

#### pop_val_a on empty ring returns 0

1. bm ring init
   - Expected: a equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
val a = bm_ring_pop_val_a()
expect(a).to_equal(0)
```

</details>

#### pop_val_b on empty ring returns 0

1. bm ring init
   - Expected: b equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
val b = bm_ring_pop_val_b()
expect(b).to_equal(0)
```

</details>

#### FIFO order: first pushed is first popped

1. bm ring init
2. bm ring push
3. bm ring push
   - Expected: k1 equals `10`
   - Expected: k2 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(10, 1000, 11, 12)
bm_ring_push(20, 2000, 21, 22)
val k1 = bm_ring_pop_kind()
val k2 = bm_ring_pop_kind()
expect(k1).to_equal(10)
expect(k2).to_equal(20)
```

</details>

### bm_ring reset via init

#### bm_ring_init after pushes resets count to 0

1. bm ring init
2. bm ring push
3. bm ring push
4. bm ring init
   - Expected: bm_ring_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(1, 10, 1, 2)
bm_ring_push(2, 20, 3, 4)
bm_ring_init()
expect(bm_ring_count()).to_equal(0)
```

</details>

#### pop after reset returns 0

1. bm ring init
2. bm ring push
3. bm ring init
   - Expected: k equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_ring_push(5, 50, 55, 66)
bm_ring_init()
val k = bm_ring_pop_kind()
expect(k).to_equal(0)
```

</details>

### bm_save_checkpoint

#### bm_save_checkpoint stores and bm_restore_checkpoint retrieves by id

1. bm ring init
2. bm save checkpoint
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_save_checkpoint(1, 500, 0x1000, 0x2000)
val r = bm_restore_checkpoint(1)
var ok = false
if val Ok(cp) = r:
    ok = cp.cycle == 500
expect(ok).to_equal(true)
```

</details>

#### bm_restore_checkpoint retrieves correct pc

1. bm ring init
2. bm save checkpoint
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_save_checkpoint(2, 100, 0xABCD, 0xEF00)
val r = bm_restore_checkpoint(2)
var ok = false
if val Ok(cp) = r:
    ok = cp.pc == 0xABCD
expect(ok).to_equal(true)
```

</details>

#### bm_restore_checkpoint retrieves correct sp

1. bm ring init
2. bm save checkpoint
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_save_checkpoint(3, 200, 0x100, 0x900)
val r = bm_restore_checkpoint(3)
var ok = false
if val Ok(cp) = r:
    ok = cp.sp == 0x900
expect(ok).to_equal(true)
```

</details>

#### bm_restore_checkpoint for unknown id returns Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = bm_restore_checkpoint(999)
var is_err = true
if val Ok(_) = r:
    is_err = false
expect(is_err).to_equal(true)
```

</details>

#### bm_save_checkpoint updates existing id

1. bm ring init
2. bm save checkpoint
3. bm save checkpoint
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_save_checkpoint(10, 100, 0x100, 0x200)
bm_save_checkpoint(10, 200, 0x300, 0x400)
val r = bm_restore_checkpoint(10)
var ok = false
if val Ok(cp) = r:
    ok = cp.cycle == 200
expect(ok).to_equal(true)
```

</details>

### bm_restore_checkpoint cycle and pc match

#### save then restore — cycle and pc match

1. bm ring init
2. bm save checkpoint
   - Expected: cycle_ok is true
   - Expected: pc_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_ring_init()
bm_save_checkpoint(20, 999, 0xDEAD, 0xBEEF)
val r = bm_restore_checkpoint(20)
var cycle_ok = false
if val Ok(cp) = r:
    cycle_ok = cp.cycle == 999
expect(cycle_ok).to_equal(true)
val r2 = bm_restore_checkpoint(20)
var pc_ok = false
if val Ok(cp2) = r2:
    pc_ok = cp2.pc == 0xDEAD
expect(pc_ok).to_equal(true)
```

</details>

### bm_find_checkpoint_before

#### finds checkpoint with highest cycle <= target

1. bm clear checkpoints
2. bm ring init
3. bm save checkpoint
4. bm save checkpoint
5. bm save checkpoint
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_clear_checkpoints()
bm_ring_init()
bm_save_checkpoint(31, 100, 0x100, 0x200)
bm_save_checkpoint(32, 200, 0x300, 0x400)
bm_save_checkpoint(33, 300, 0x500, 0x600)
val maybe = bm_find_checkpoint_before(250)
var ok = false
if val Some(cp) = maybe:
    ok = cp.cycle == 200
expect(ok).to_equal(true)
```

</details>

#### finds checkpoint exactly at cycle boundary

1. bm clear checkpoints
2. bm ring init
3. bm save checkpoint
4. bm save checkpoint
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_clear_checkpoints()
bm_ring_init()
bm_save_checkpoint(41, 100, 0x10, 0x20)
bm_save_checkpoint(42, 200, 0x30, 0x40)
val maybe = bm_find_checkpoint_before(200)
var ok = false
if val Some(cp) = maybe:
    ok = cp.cycle == 200
expect(ok).to_equal(true)
```

</details>

#### returns None when all checkpoints are after target

1. bm clear checkpoints
2. bm ring init
3. bm save checkpoint
4. bm save checkpoint
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_clear_checkpoints()
bm_ring_init()
bm_save_checkpoint(51, 500, 0x10, 0x20)
bm_save_checkpoint(52, 600, 0x30, 0x40)
val maybe = bm_find_checkpoint_before(100)
var is_none = true
if val Some(_) = maybe:
    is_none = false
expect(is_none).to_equal(true)
```

</details>

#### finds highest cycle — 3 checkpoints at 100/200/300, before 250 gives 200

1. bm clear checkpoints
2. bm ring init
3. bm save checkpoint
4. bm save checkpoint
5. bm save checkpoint
   - Expected: cycle equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
bm_clear_checkpoints()
bm_ring_init()
bm_save_checkpoint(61, 100, 0xA, 0xB)
bm_save_checkpoint(62, 200, 0xC, 0xD)
bm_save_checkpoint(63, 300, 0xE, 0xF)
val maybe = bm_find_checkpoint_before(250)
var cycle = -1
if val Some(cp) = maybe:
    cycle = cp.cycle
expect(cycle).to_equal(200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_baremetal_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bm_replay mode
- bm_ring init and count
- bm_ring push and count
- bm_ring push and pop
- bm_ring reset via init
- bm_save_checkpoint
- bm_restore_checkpoint cycle and pc match
- bm_find_checkpoint_before

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

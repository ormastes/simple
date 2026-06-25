# dbfs_engine_checkpoint_ring_spec

> DBFS Checkpoint Ring Disk Persistence Specification

<!-- sdn-diagram:id=dbfs_engine_checkpoint_ring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_checkpoint_ring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_checkpoint_ring_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_checkpoint_ring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_engine_checkpoint_ring_spec

DBFS Checkpoint Ring Disk Persistence Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_engine_checkpoint_ring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Checkpoint Ring Disk Persistence Specification

Verifies R2 HIGH-risk gap: checkpoint ring is written to META_DURABLE
and remount reads the correct slot.

  1. ring slot is present after remount
  2. correct (latest clean=true) slot is selected on remount
  3. ring slot is written to META_DURABLE arena
  4. stale dirty slots are not returned as current

## Scenarios

### DBFS Checkpoint Ring — disk persistence
_Ring slot survives simulated remount._

#### ring slot written before remount is readable after

- ring write slot
- ring flush
- ring close
   - Expected: got.slot_gen equals `5`
   - Expected: got.clean is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
val slot = RingSlot(slot_gen: 5, clean: true, btree_root_page: 100)
ring.write_slot(0, slot).unwrap()
ring.flush().unwrap()
ring.close().unwrap()
val ring2 = CheckpointRing.reopen()
val got = ring2.read_slot(0).unwrap()
expect(got.slot_gen).to_equal(5)
expect(got.clean).to_equal(true)
```

</details>

#### highest ring slot survives remount

- btree root page:
- ring flush
- ring close
   - Expected: slot.slot_gen equals `RING_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
CheckpointRing.persist_slot(RING_SIZE - 1, RingSlot(
    slot_gen: RING_SIZE,
    clean: true,
    btree_root_page: (RING_SIZE - 1) * 8
))
ring.flush().unwrap()
ring.close().unwrap()
val ring2 = CheckpointRing.reopen()
val slot = ring2.read_slot(RING_SIZE - 1).unwrap()
expect(slot.slot_gen).to_equal(RING_SIZE)
```

</details>

### DBFS Checkpoint Ring — best slot selection
_Remount picks the slot with highest gen and clean=true._

#### current_slot returns slot with highest gen and clean=true

- ring write slot
- ring write slot
- ring write slot
- ring flush
- ring close
   - Expected: best.slot_gen equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(slot_gen: 3, clean: true, btree_root_page: 30)).unwrap()
ring.write_slot(1, RingSlot(slot_gen: 5, clean: true, btree_root_page: 50)).unwrap()
ring.write_slot(2, RingSlot(slot_gen: 4, clean: false, btree_root_page: 40)).unwrap()
ring.flush().unwrap()
ring.close().unwrap()
val ring2 = CheckpointRing.reopen()
val best = ring2.current_slot().unwrap()
expect(best.slot_gen).to_equal(5)
```

</details>

#### dirty slots are not selected as current

- ring write slot
- ring write slot
- ring flush
- ring close
   - Expected: best.slot_gen equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(slot_gen: 10, clean: false, btree_root_page: 10)).unwrap()
ring.write_slot(1, RingSlot(slot_gen: 2, clean: true, btree_root_page: 20)).unwrap()
ring.flush().unwrap()
ring.close().unwrap()
val ring2 = CheckpointRing.reopen()
val best = ring2.current_slot().unwrap()
expect(best.slot_gen).to_equal(2)
```

</details>

### DBFS Checkpoint Ring — storage class
_Ring writes must target META_DURABLE arena._

#### ring write uses META_DURABLE storage class

- ring write slot
- ring flush
   - Expected: sc equals `StorageClass.MetaDurable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(slot_gen: 1, clean: true, btree_root_page: 0)).unwrap()
ring.flush().unwrap()
val sc = ring.last_write_storage_class()
expect(sc).to_equal(StorageClass.MetaDurable)
```

</details>

#### ring size constant is at least 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RING_SIZE >= 4).to_equal(true)
```

</details>

### DBFS Checkpoint Ring — callback persistence
_When callback is registered, writes go through the callback path._

#### callback path persists slots across reopen

- ring clear persist callback
- ring register persist callback
   - Expected: ring_is_callback_registered() is true
- ring write slot
- ring flush
- ring close
   - Expected: ring_cb_slot_count() equals `1`
   - Expected: got.slot_gen equals `7`
- ring clear persist callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ring_clear_persist_callback()
ring_register_persist_callback("arena:META_DURABLE")
expect(ring_is_callback_registered()).to_equal(true)
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(slot_gen: 7, clean: true, btree_root_page: 70)).unwrap()
ring.flush().unwrap()
ring.close().unwrap()
expect(ring_cb_slot_count()).to_equal(1)
val ring2 = CheckpointRing.reopen()
val got = ring2.read_slot(0).unwrap()
expect(got.slot_gen).to_equal(7)
ring_clear_persist_callback()
```

</details>

#### callback registration is clearable

- ring register persist callback
   - Expected: ring_is_callback_registered() is true
- ring clear persist callback
   - Expected: ring_is_callback_registered() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ring_register_persist_callback("test")
expect(ring_is_callback_registered()).to_equal(true)
ring_clear_persist_callback()
expect(ring_is_callback_registered()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

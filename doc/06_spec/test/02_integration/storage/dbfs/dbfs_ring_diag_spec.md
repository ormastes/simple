# Dbfs Ring Diag Specification

> 1. ring write slot

<!-- sdn-diagram:id=dbfs_ring_diag_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_ring_diag_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_ring_diag_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_ring_diag_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Ring Diag Specification

## Scenarios

### DBFS Ring Diagnostic

#### single write_slot then read_slot works

1. ring write slot
   - Expected: slot.gen equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(gen: 42, clean: true, btree_root_page: 100)).unwrap()
val slot = ring.read_slot(0).unwrap()
expect(slot.gen).to_equal(42)
```

</details>

<details>
<summary>Advanced: loop persist_slot 5 times then current_store reflects all entries</summary>

#### loop persist_slot 5 times then current_store reflects all entries

1.  persist 5 slots
   - Expected: store.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
_persist_5_slots()
val store = ring.current_store()
expect(store.len()).to_equal(5)
```

</details>


</details>

#### two separate writes then read_slot 1 works

1. ring write slot
2. ring write slot
   - Expected: s1.gen equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(gen: 10, clean: true, btree_root_page: 0)).unwrap()
ring.write_slot(1, RingSlot(gen: 11, clean: true, btree_root_page: 1)).unwrap()
val s1 = ring.read_slot(1).unwrap()
expect(s1.gen).to_equal(11)
```

</details>

#### current_store has entries after writes

1. ring write slot
2. ring write slot
   - Expected: store.len() >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(gen: 1, clean: true, btree_root_page: 0)).unwrap()
ring.write_slot(1, RingSlot(gen: 2, clean: true, btree_root_page: 1)).unwrap()
val store = ring.current_store()
expect(store.len() >= 2).to_equal(true)
```

</details>

#### flush then reopen: read slot 0

1. ring write slot
2. ring flush
3. ring close
   - Expected: s.gen equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
ring.write_slot(0, RingSlot(gen: 7, clean: true, btree_root_page: 70)).unwrap()
ring.flush().unwrap()
ring.close().unwrap()
val ring2 = CheckpointRing.reopen()
val s = ring2.read_slot(0).unwrap()
expect(s.gen).to_equal(7)
```

</details>

#### persisting the highest slot then reopen sees that slot

1. btree root page:
2. ring flush
3. ring close
   - Expected: slot.gen equals `RING_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ring = CheckpointRing.new_persistent()
CheckpointRing.persist_slot(RING_SIZE - 1, RingSlot(
    gen: RING_SIZE,
    clean: true,
    btree_root_page: (RING_SIZE - 1) * 8
))
ring.flush().unwrap()
ring.close().unwrap()
val ring2 = CheckpointRing.reopen()
val slot = ring2.read_slot(RING_SIZE - 1).unwrap()
expect(slot.gen).to_equal(RING_SIZE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_ring_diag_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DBFS Ring Diagnostic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

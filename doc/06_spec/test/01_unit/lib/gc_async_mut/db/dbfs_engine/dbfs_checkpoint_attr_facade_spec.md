# Dbfs Checkpoint Attr Facade Specification

> 1. var pager = DbfsPager new

<!-- sdn-diagram:id=dbfs_checkpoint_attr_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_checkpoint_attr_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_checkpoint_attr_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_checkpoint_attr_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Checkpoint Attr Facade Specification

## Scenarios

### gc_async_mut DBFS checkpoint and attribute facade

#### re-exports pager, checkpoint, and attribute-index contracts

1. var pager = DbfsPager new
2. var data = PageData zeroed
3. data set byte
   - Expected: pager.write_page(page, data).is_ok() is true
   - Expected: pager.dirty_count() equals `1`
   - Expected: pager.flush_dirty().unwrap() equals `1`
   - Expected: pager.read_page(page).unwrap().byte_at(0) equals `0x41`
   - Expected: RING_SIZE >= 4 is true
   - Expected: ring.write_slot(0, RingSlot(gen: 9, clean: true, btree_root_page: 44)).is_ok() is true
   - Expected: ring.current_slot().unwrap().gen equals `9`
4. var ckpt = DbfsCheckpoint new
   - Expected: ckpt.publish(CheckpointRoot(btree_root: PageId(id: 7), gen: 7)).is_ok() is true
   - Expected: ckpt.current_root().unwrap().btree_root.id equals `7`
5. var inodes = InodeTable new
   - Expected: inodes.insert(a).is_ok() is true
   - Expected: inodes.insert(b).is_ok() is true
6. var index = AttrIndexManager new
7. index build from inodes
   - Expected: index.count() equals `2`
   - Expected: size_result.ino_ids.len() equals `1`
   - Expected: size_result.ino_ids[0] equals `10`
   - Expected: uid_result.ino_ids[0] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PAGE_SIZE_BYTES).to_equal(8192)
var pager = DbfsPager.new(2)
val page = pager.alloc_page().unwrap()
var data = PageData.zeroed()
data.set_byte(0, 0x41)
expect(pager.write_page(page, data).is_ok()).to_equal(true)
expect(pager.dirty_count()).to_equal(1)
expect(pager.flush_dirty().unwrap()).to_equal(1)
expect(pager.read_page(page).unwrap().byte_at(0)).to_equal(0x41)

val ring = CheckpointRing.new_persistent()
expect(RING_SIZE >= 4).to_equal(true)
expect(ring.write_slot(0, RingSlot(gen: 9, clean: true, btree_root_page: 44)).is_ok()).to_equal(true)
expect(ring.current_slot().unwrap().gen).to_equal(9)
var ckpt = DbfsCheckpoint.new()
expect(ckpt.publish(CheckpointRoot(btree_root: PageId(id: 7), gen: 7)).is_ok()).to_equal(true)
expect(ckpt.current_root().unwrap().btree_root.id).to_equal(7)

var inodes = InodeTable.new()
val a = InodeRow(ino_id: 10, gen: 1, mode: 420, uid: 1000, gid: 1000, link_count: 1, size: 5, mtime: 1, ctime: 1, flags: 0)
val b = InodeRow(ino_id: 11, gen: 1, mode: 420, uid: 2000, gid: 2000, link_count: 1, size: 8, mtime: 2, ctime: 2, flags: 0)
expect(inodes.insert(a).is_ok()).to_equal(true)
expect(inodes.insert(b).is_ok()).to_equal(true)
var index = AttrIndexManager.new()
index.build_from_inodes(inodes)
expect(index.count()).to_equal(2)
val size_result = index.query(AttrQuery(attribute: ATTR_SIZE, op: AttrOp.Eq(value: "00000000000000000005")))
expect(size_result.ino_ids.len()).to_equal(1)
expect(size_result.ino_ids[0]).to_equal(10)
val uid_result = index.query(AttrQuery(attribute: ATTR_UID, op: AttrOp.Eq(value: "00000000000000002000")))
expect(uid_result.ino_ids[0]).to_equal(11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut DBFS checkpoint and attribute facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Dbfs Checkpoint Attr Facade Specification

> Tests covering nogc_async_mut DBFS checkpoint and attribute facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Checkpoint Attr Facade Specification

## Scenarios

### nogc_async_mut DBFS checkpoint and attribute facade

#### re-exports pager, checkpoint, and attribute-index contracts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports pager, checkpoint, and attribute-index contracts
   - Expected: PAGE_SIZE_BYTES equals `8192`
   - Expected: pager.write_page(page, data).is_ok() is true
   - Expected: pager.dirty_count() equals `1`
   - Expected: pager.flush_dirty().unwrap() equals `1`
   - Expected: pager.read_page(page).unwrap().byte_at(0) equals `0x41`
   - Expected: RING_SIZE >= 4 is true
   - Expected: ring.write_slot(0, RingSlot(gen: 9, clean: true, btree_root_page: 44)).is_ok() is true
   - Expected: ring.current_slot().unwrap().gen equals `9`
   - Expected: ckpt.publish(CheckpointRoot(btree_root: PageId(id: 7), gen: 7)).is_ok() is true
   - Expected: ckpt.current_root().unwrap().btree_root.id equals `7`
   - Expected: inodes.insert(a).is_ok() is true
   - Expected: inodes.insert(b).is_ok() is true
   - Expected: index.count() equals `2`
   - Expected: size_result.ino_ids.len() equals `1`
   - Expected: size_result.ino_ids[0] equals `10`
   - Expected: uid_result.ino_ids[0] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports pager, checkpoint, and attribute-index contracts")
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
| Source | `test/unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut DBFS checkpoint and attribute facade.
- nogc_async_mut DBFS checkpoint and attribute facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1031529888a66294d96a0f57d4c113691da1ba19eba0ef0667726b0b7d18d4e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1031529888a66294d96a0f57d4c113691da1ba19eba0ef0667726b0b7d18d4e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1031529888a66294d96a0f57d4c113691da1ba19eba0ef0667726b0b7d18d4e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports pager, checkpoint, and attribute-index contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

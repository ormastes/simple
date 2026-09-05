# Storage Shared Facade Specification

> Tests covering gc_async_mut storage shared facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Shared Facade Specification

## Scenarios

### gc_async_mut storage shared facade

#### re-exports wal and btree primitives

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports wal and btree primitives
   - Expected: lsn.value equals `1`
   - Expected: wal.read_record(Lsn(value: 1)).unwrap().payload equals `payload`
   - Expected: wal.flush_wal().is_ok() is true
   - Expected: wal.get_durable_lsn().value equals `1`
   - Expected: WAL_RECORD_COMMIT equals `3`
   - Expected: tree.insert(BTreeKey(a: 1, b: 2), "value").is_ok() is true
   - Expected: found equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports wal and btree primitives")
var wal = SharedWal.new()
val lsn = wal.append(WalRecord(txn_id: 7, record_type: WAL_RECORD_DATA, payload: "payload")).unwrap()
expect(lsn.value).to_equal(1)
expect(wal.read_record(Lsn(value: 1)).unwrap().payload).to_equal("payload")
expect(wal.flush_wal().is_ok()).to_equal(true)
expect(wal.get_durable_lsn().value).to_equal(1)
expect(WAL_RECORD_COMMIT).to_equal(3)

var tree = BTree<text>.new(2)
expect(tree.insert(BTreeKey(a: 1, b: 2), "value").is_ok()).to_equal(true)
val found = tree.lookup(BTreeKey(a: 1, b: 2)).unwrap()
expect(found).to_equal("value")
```

</details>

#### re-exports checkpoint ring and intent log persistence helpers

- re-exports checkpoint ring and intent log persistence helpers
   - Expected: ring_is_callback_registered() is true
   - Expected: ring_persist_callback_tag() equals `facade-ring`
   - Expected: ring.write_slot(0, RingSlot(slot_gen: 2, clean: true, btree_root_page: 99)).is_ok() is true
   - Expected: ring_cb_slot_count() equals `1`
   - Expected: ring.latest_clean().unwrap().btree_root_page equals `99`
   - Expected: intent_is_callback_registered() is true
   - Expected: intent_persist_callback_tag() equals `facade-intent`
   - Expected: log.append(IntentLogRecord(txn_id: 1, lsn: 5, committed: true)).is_ok() is true
   - Expected: log.flush().is_ok() is true
   - Expected: intent_cb_record_count() equals `1`
   - Expected: log.head_pointer().tail_lsn equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports checkpoint ring and intent log persistence helpers")
ring_clear_persist_callback()
ring_register_persist_callback("facade-ring")
expect(ring_is_callback_registered()).to_equal(true)
expect(ring_persist_callback_tag()).to_equal("facade-ring")
var ring = SharedCheckpointRing.new_with_size(4)
expect(ring.write_slot(0, RingSlot(slot_gen: 2, clean: true, btree_root_page: 99)).is_ok()).to_equal(true)
expect(ring_cb_slot_count()).to_equal(1)
expect(ring.latest_clean().unwrap().btree_root_page).to_equal(99)

intent_clear_persist_callback()
intent_register_persist_callback("facade-intent")
expect(intent_is_callback_registered()).to_equal(true)
expect(intent_persist_callback_tag()).to_equal("facade-intent")
var log = SharedIntentLog.new_persistent()
expect(log.append(IntentLogRecord(txn_id: 1, lsn: 5, committed: true)).is_ok()).to_equal(true)
log.set_head(5)
expect(log.flush().is_ok()).to_equal(true)
expect(intent_cb_record_count()).to_equal(1)
expect(log.head_pointer().tail_lsn).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut storage shared facade.
- gc_async_mut storage shared facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `e5a45c65959e9ffe81ca1e22cb5f9e2fd3cbdabf5341147b0c3e42e3c45dbe1f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5a45c65959e9ffe81ca1e22cb5f9e2fd3cbdabf5341147b0c3e42e3c45dbe1f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5a45c65959e9ffe81ca1e22cb5f9e2fd3cbdabf5341147b0c3e42e3c45dbe1f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports wal and btree primitives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports checkpoint ring and intent log persistence helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

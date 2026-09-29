# Dbfs Recovery Namespace Facade Specification

> Tests covering gc_async_mut DBFS recovery namespace facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Recovery Namespace Facade Specification

## Scenarios

### gc_async_mut DBFS recovery namespace facade

#### re-exports namespace, intent-log, and recovery contracts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports namespace, intent-log, and recovery contracts
   - Expected: tree.insert(NsDentryKey(parent_ino: 1, name_hash: 22), NsIno(value: 2)).is_ok() is true
   - Expected: tree.lookup(NsDentryKey(parent_ino: 1, name_hash: 22)).unwrap().value equals `2`
   - Expected: log.append(IntentLogRecord(txn_id: 1, lsn: 10, committed: true)).is_ok() is true
   - Expected: log.append(IntentLogRecord(txn_id: 2, lsn: 11, committed: false)).is_ok() is true
   - Expected: log.flush().is_ok() is true
   - Expected: log.scan_committed().unwrap().len() equals `1`
   - Expected: recovered.superblock_gen equals `3`
   - Expected: recovered.replayed_txn_ids.len() equals `1`
   - Expected: recovery_get_discarded_ids()[0] equals `99`
   - Expected: recovery_get_checkpoint_gen() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports namespace, intent-log, and recovery contracts")
var tree = NsBTree.new()
expect(tree.insert(NsDentryKey(parent_ino: 1, name_hash: 22), NsIno(value: 2)).is_ok()).to_equal(true)
expect(tree.lookup(NsDentryKey(parent_ino: 1, name_hash: 22)).unwrap().value).to_equal(2)

val log = IntentLog.new_persistent()
expect(log.append(IntentLogRecord(txn_id: 1, lsn: 10, committed: true)).is_ok()).to_equal(true)
expect(log.append(IntentLogRecord(txn_id: 2, lsn: 11, committed: false)).is_ok()).to_equal(true)
expect(log.flush().is_ok()).to_equal(true)
expect(log.scan_committed().unwrap().len()).to_equal(1)

recovery_clear_callbacks()
recovery_register_discard_cb("arena")
recovery_register_checkpoint_cb("checkpoint")
val device = FaultDevice(
    replicas: [SuperblockReplica(generation: 3, crc_valid: true)],
    wal_entries: [
        FaultWalEntry(txn_id: 10, committed: true, lsn: 1),
        FaultWalEntry(txn_id: 11, committed: false, lsn: 2)
    ],
    orphan_arenas: [99],
    fault_after: -1,
    last_clean_gen: 3
)
val recovered = DbfsRecovery.recover(device).unwrap()
expect(recovered.superblock_gen).to_equal(3)
expect(recovered.replayed_txn_ids.len()).to_equal(1)
expect(recovery_get_discarded_ids()[0]).to_equal(99)
expect(recovery_get_checkpoint_gen()).to_equal(4)
recovery_clear_callbacks()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut DBFS recovery namespace facade.
- gc_async_mut DBFS recovery namespace facade

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

- Canonical SPipe generation for source `3169e9f7fc0c366143d38daa096c5918df1a5da8eb716998f7ab0eeacb5b4020`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3169e9f7fc0c366143d38daa096c5918df1a5da8eb716998f7ab0eeacb5b4020`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3169e9f7fc0c366143d38daa096c5918df1a5da8eb716998f7ab0eeacb5b4020`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports namespace, intent-log, and recovery contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

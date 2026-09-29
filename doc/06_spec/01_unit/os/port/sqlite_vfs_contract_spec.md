# @manual: primary

> Purpose: Prove that SQLite lock ladder -> flock op mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that SQLite lock ladder -> flock op mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/sqlite_vfs_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SQLite lock ladder -> flock op mapping.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-PORT-001
doc/01_research/local/REQ-OS-PORT-001.md
doc/03_plan/sys_test/REQ-OS-PORT-001.md
doc/04_architecture/REQ-OS-PORT-001.md
doc/05_design/REQ-OS-PORT-001.md

## Scenarios

### SQLite lock ladder -> flock op mapping

#### maps NONE to LOCK_UN

- Verify: maps NONE to LOCK_UN
   - Expected: flock_op_for(SqliteLockLevel.LockNone) equals `LOCK_UN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: maps NONE to LOCK_UN")
expect(flock_op_for(SqliteLockLevel.LockNone)).to_equal("LOCK_UN")
```

</details>

#### maps SHARED to LOCK_SH

- Verify: maps SHARED to LOCK_SH
   - Expected: flock_op_for(SqliteLockLevel.LockShared) equals `LOCK_SH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: maps SHARED to LOCK_SH")
expect(flock_op_for(SqliteLockLevel.LockShared)).to_equal("LOCK_SH")
```

</details>

#### maps RESERVED onto LOCK_SH (whole-file flock approximation)

- Verify: maps RESERVED onto LOCK_SH (whole-file flock approximation)
   - Expected: flock_op_for(SqliteLockLevel.LockReserved) equals `LOCK_SH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: maps RESERVED onto LOCK_SH (whole-file flock approximation)")
expect(flock_op_for(SqliteLockLevel.LockReserved)).to_equal("LOCK_SH")
```

</details>

#### maps PENDING onto LOCK_EX (whole-file flock approximation)

- Verify: maps PENDING onto LOCK_EX (whole-file flock approximation)
   - Expected: flock_op_for(SqliteLockLevel.LockPending) equals `LOCK_EX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: maps PENDING onto LOCK_EX (whole-file flock approximation)")
expect(flock_op_for(SqliteLockLevel.LockPending)).to_equal("LOCK_EX")
```

</details>

#### maps EXCLUSIVE to LOCK_EX

- Verify: maps EXCLUSIVE to LOCK_EX
   - Expected: flock_op_for(SqliteLockLevel.LockExclusive) equals `LOCK_EX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: maps EXCLUSIVE to LOCK_EX")
expect(flock_op_for(SqliteLockLevel.LockExclusive)).to_equal("LOCK_EX")
```

</details>

#### flags SHARED and EXCLUSIVE as exact whole-file equivalents

- Verify: flags SHARED and EXCLUSIVE as exact whole-file equivalents
   - Expected: flock_mapping_is_exact(SqliteLockLevel.LockShared) is true
   - Expected: flock_mapping_is_exact(SqliteLockLevel.LockExclusive) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: flags SHARED and EXCLUSIVE as exact whole-file equivalents")
expect(flock_mapping_is_exact(SqliteLockLevel.LockShared)).to_equal(true)
expect(flock_mapping_is_exact(SqliteLockLevel.LockExclusive)).to_equal(true)
```

</details>

#### flags RESERVED and PENDING as inexact (byte-range intent not representable)

- Verify: flags RESERVED and PENDING as inexact (byte-range intent not representable)
   - Expected: flock_mapping_is_exact(SqliteLockLevel.LockReserved) is false
   - Expected: flock_mapping_is_exact(SqliteLockLevel.LockPending) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: flags RESERVED and PENDING as inexact (byte-range intent not representable)")
expect(flock_mapping_is_exact(SqliteLockLevel.LockReserved)).to_equal(false)
expect(flock_mapping_is_exact(SqliteLockLevel.LockPending)).to_equal(false)
```

</details>

#### names the lock levels for the audit table

- Verify: names the lock levels for the audit table
   - Expected: sqlite_lock_level_name(SqliteLockLevel.LockShared) equals `SHARED`
   - Expected: sqlite_lock_level_name(SqliteLockLevel.LockExclusive) equals `EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: names the lock levels for the audit table")
expect(sqlite_lock_level_name(SqliteLockLevel.LockShared)).to_equal("SHARED")
expect(sqlite_lock_level_name(SqliteLockLevel.LockExclusive)).to_equal("EXCLUSIVE")
```

</details>

### shared-memory (shm) methods fail closed, gating WAL

#### reports xShmMap unsupported (not fake-supported)

- Verify: reports xShmMap unsupported (not fake-supported)
   - Expected: method_report("xShmMap").status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: reports xShmMap unsupported (not fake-supported)")
expect(method_report("xShmMap").status).to_equal("unsupported")
```

</details>

#### reports xShmLock / xShmBarrier / xShmUnmap unsupported

- Verify: reports xShmLock / xShmBarrier / xShmUnmap unsupported
   - Expected: method_report("xShmLock").status equals `unsupported`
   - Expected: method_report("xShmBarrier").status equals `unsupported`
   - Expected: method_report("xShmUnmap").status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: reports xShmLock / xShmBarrier / xShmUnmap unsupported")
expect(method_report("xShmLock").status).to_equal("unsupported")
expect(method_report("xShmBarrier").status).to_equal("unsupported")
expect(method_report("xShmUnmap").status).to_equal("unsupported")
```

</details>

#### shared mmap facility itself is unsupported

- Verify: shared mmap facility itself is unsupported
   - Expected: posix_mmap_shared_status() equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: shared mmap facility itself is unsupported")
expect(posix_mmap_shared_status()).to_equal("unsupported")
```

</details>

#### gates WAL mode off because xShmMap is unsupported

- Verify: gates WAL mode off because xShmMap is unsupported
   - Expected: wal_mode_supported() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: gates WAL mode off because xShmMap is unsupported")
# Honest-failure oracle: if xShmMap ever falsely reported supported,
# this must fail. Restore proves the gate is wired to the real status.
expect(wal_mode_supported()).to_equal(false)
```

</details>

#### names the exact WAL prerequisite

- Verify: names the exact WAL prerequisite


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: names the exact WAL prerequisite")
expect(wal_blocked_prerequisite()).to_contain("shared mmap")
```

</details>

### rollback-journal mode is the supported path

#### reports rollback-journal (DELETE) mode supported

- Verify: reports rollback-journal (DELETE) mode supported
   - Expected: rollback_journal_mode_supported() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: reports rollback-journal (DELETE) mode supported")
expect(rollback_journal_mode_supported()).to_equal(true)
```

</details>

#### keeps core file methods supported

- Verify: keeps core file methods supported
   - Expected: method_report("xOpen").status equals `supported`
   - Expected: method_report("xRead").status equals `supported`
   - Expected: method_report("xWrite").status equals `supported`
   - Expected: method_report("xFileSize").status equals `supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: keeps core file methods supported")
expect(method_report("xOpen").status).to_equal("supported")
expect(method_report("xRead").status).to_equal("supported")
expect(method_report("xWrite").status).to_equal("supported")
expect(method_report("xFileSize").status).to_equal("supported")
```

</details>

#### reports xSync partial (durability proof pending), still functional

- Verify: reports xSync partial (durability proof pending), still functional
   - Expected: method_report("xSync").status equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: reports xSync partial (durability proof pending), still functional")
expect(method_report("xSync").status).to_equal("partial")
```

</details>

#### reports xLock partial (flock advisory, no blocking)

- Verify: reports xLock partial (flock advisory, no blocking)
   - Expected: method_report("xLock").status equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: reports xLock partial (flock advisory, no blocking)")
expect(method_report("xLock").status).to_equal("partial")
```

</details>

#### reports xTruncate unsupported (no VFS truncate; DELETE mode unaffected)

- Verify: reports xTruncate unsupported (no VFS truncate; DELETE mode unaffected)
   - Expected: method_report("xTruncate").status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: reports xTruncate unsupported (no VFS truncate; DELETE mode unaffected)")
expect(method_report("xTruncate").status).to_equal("unsupported")
```

</details>

### published block durability characteristics (§8 contract)

#### publishes a 512-byte sector size

- Verify: publishes a 512-byte sector size
   - Expected: published_durability_flags().sector_size equals `512u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: publishes a 512-byte sector size")
expect(published_durability_flags().sector_size).to_equal(512u32)
```

</details>

#### publishes a flush/fsync path

- Verify: publishes a flush/fsync path
   - Expected: published_durability_flags().has_flush is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: publishes a flush/fsync path")
expect(published_durability_flags().has_flush).to_equal(true)
```

</details>

#### does NOT claim atomic-write or powersafe-overwrite (unproven -> false)

- Verify: does NOT claim atomic-write or powersafe-overwrite (unproven -> false)
   - Expected: published_durability_flags().has_atomic_write is false
   - Expected: published_durability_flags().powersafe_overwrite is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: does NOT claim atomic-write or powersafe-overwrite (unproven -> false)")
expect(published_durability_flags().has_atomic_write).to_equal(false)
expect(published_durability_flags().powersafe_overwrite).to_equal(false)
```

</details>

### method status tally is honest

#### counts 6 supported methods

- Verify: counts 6 supported methods
   - Expected: count_with_status("supported") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: counts 6 supported methods")
expect(count_with_status("supported")).to_equal(6)
```

</details>

#### counts 6 partial methods

- Verify: counts 6 partial methods
   - Expected: count_with_status("partial") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: counts 6 partial methods")
expect(count_with_status("partial")).to_equal(6)
```

</details>

#### counts 5 unsupported methods

- Verify: counts 5 unsupported methods
   - Expected: count_with_status("unsupported") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: counts 5 unsupported methods")
expect(count_with_status("unsupported")).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-PORT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b40a5efbe37ee91c576e0b4426679082192fe3eeda6efdf179fc29fdc0e39204`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b40a5efbe37ee91c576e0b4426679082192fe3eeda6efdf179fc29fdc0e39204`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b40a5efbe37ee91c576e0b4426679082192fe3eeda6efdf179fc29fdc0e39204`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/sqlite_vfs_contract_spec.spl
mirror: doc/06_spec/01_unit/os/port/sqlite_vfs_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/sqlite_vfs_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/sqlite_vfs_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/sqlite_vfs_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/port/sqlite_vfs_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/port/sqlite_vfs_contract_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps NONE to LOCK_UN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/sqlite_vfs_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps SHARED to LOCK_SH' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/sqlite_vfs_contract_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps RESERVED onto LOCK_SH (whole-file flock approximation)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

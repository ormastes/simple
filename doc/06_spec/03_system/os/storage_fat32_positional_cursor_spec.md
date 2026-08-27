# FAT32 Positional Cursor Preservation

> System-level regression check for FR-STORAGE-0002. FAT32 positional I/O uses

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 Positional Cursor Preservation

System-level regression check for FR-STORAGE-0002. FAT32 positional I/O uses

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/storage_fat32_positional_cursor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

System-level regression check for FR-STORAGE-0002. FAT32 positional I/O uses
save/seek/operation/restore, so cursor restoration must preserve size changes.

## Scenarios

### FAT32 positional cursor preservation

#### seek updates the open-file cursor

- seek updates the open-file cursor
   - Expected: seek_r.is_ok() is true
   - Expected: file.position equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("seek updates the open-file cursor")
"""Seek replaces the stored open-file entry with the requested offset."""
var driver = cursor_driver()
val seek_r = driver.seek(_fat32_pack_handle(0, 1u32), 0)
expect(seek_r.is_ok()).to_equal(true)
val file = driver.open_files[0]
expect(file.position).to_equal(0)
```

</details>

#### cursor restore keeps file size while restoring saved position

- cursor restore keeps file size while restoring saved position
   - Expected: restore.is_ok() is true
   - Expected: file.position equals `10`
   - Expected: file.current_cluster equals `2`
   - Expected: file.size equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cursor restore keeps file size while restoring saved position")
"""Restoring a saved cursor preserves any file-size growth already recorded."""
var driver = cursor_driver()
driver.seek(_fat32_pack_handle(0, 1u32), 0)
val current = driver.open_files[0]
driver.open_files.remove(0)
driver.open_files.push(OpenFile(
    start_cluster: current.start_cluster,
    current_cluster: current.current_cluster,
    position: current.position,
    size: 96,
    is_dir: current.is_dir,
    is_open: current.is_open,
    generation: current.generation
))
val restore = driver.restore_open_file_cursor(_fat32_pack_handle(0, 1u32), 2, 10)
expect(restore.is_ok()).to_equal(true)
val file = driver.open_files[0]
expect(file.position).to_equal(10)
expect(file.current_cluster).to_equal(2)
expect(file.size).to_equal(96)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `821f724f6e8a3fe974dcc2a14c58a60593f5e01b5623d2e9f8e5c47ff167354f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `821f724f6e8a3fe974dcc2a14c58a60593f5e01b5623d2e9f8e5c47ff167354f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `821f724f6e8a3fe974dcc2a14c58a60593f5e01b5623d2e9f8e5c47ff167354f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/storage_fat32_positional_cursor_spec.spl
mirror: doc/06_spec/03_system/os/storage_fat32_positional_cursor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/storage_fat32_positional_cursor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/storage_fat32_positional_cursor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/storage_fat32_positional_cursor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/storage_fat32_positional_cursor_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seek updates the open-file cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/storage_fat32_positional_cursor_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cursor restore keeps file size while restoring saved position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

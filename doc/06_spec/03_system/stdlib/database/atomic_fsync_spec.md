# Atomic fsync Before Rename Specification

> Tests that rt_file_sync is callable and that atomic_write produces

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atomic fsync Before Rename Specification

Tests that rt_file_sync is callable and that atomic_write produces

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no implementation yet) |
| Source | `test/03_system/stdlib/database/atomic_fsync_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-5 (hardening fix), AC-7 (new tests)
Tests that rt_file_sync is callable and that atomic_write produces
durable, correct files. The fsync syscall itself is not directly
observable without a power-cut harness, so we verify:
1. rt_file_sync extern loads and returns true for valid files
2. atomic_write content integrity is preserved after the write path

## Scenarios

### rt_file_sync

### basic semantics

#### returns true for an existing file

- returns true for an existing file
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for an existing file")
val path = "/tmp/simple_db_test_fsync_valid.dat"
rt_file_write_text(path, "sync test data")
val result = rt_file_sync(path)
expect(result).to_equal(true)
cleanup_file(path)
```

</details>

#### returns false for nonexistent file

- returns false for nonexistent file
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for nonexistent file")
val result = rt_file_sync("/tmp/simple_db_nonexistent_fsync.dat")
expect(result).to_equal(false)
```

</details>

#### returns false for invalid path

- returns false for invalid path
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for invalid path")
val result = rt_file_sync("/nonexistent_dir_xyz/file.dat")
expect(result).to_equal(false)
```

</details>

### atomic_write with fsync

### content integrity

#### written content matches read content

- written content matches read content
   - Expected: read_back equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("written content matches read content")
val path = test_fsync_path()
cleanup_file(path)
val content = "hello database world"
atomic_write(path, content)
val read_back = atomic_read(path) ?? ""
expect(read_back).to_equal(content)
cleanup_file(path)
```

</details>

#### overwrites previous content atomically

- overwrites previous content atomically
   - Expected: read_back equals `version2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overwrites previous content atomically")
val path = test_fsync_path()
cleanup_file(path)
atomic_write(path, "version1")
atomic_write(path, "version2")
val read_back = atomic_read(path) ?? ""
expect(read_back).to_equal("version2")
cleanup_file(path)
```

</details>

#### handles large content

- handles large content
   - Expected: read_back equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles large content")
val path = test_fsync_path()
cleanup_file(path)
# Build a ~1KB payload
var parts: [text] = []
var i = 0
while i < 100:
    parts.push("row_data_number_{i}_with_some_padding")
    i = i + 1
val content = parts.join("\n")
atomic_write(path, content)
val read_back = atomic_read(path) ?? ""
expect(read_back).to_equal(content)
cleanup_file(path)
```

</details>

### temp file cleanup

#### no temp file remains after successful write

- no temp file remains after successful write
   - Expected: rt_file_exists(tmp_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no temp file remains after successful write")
val path = test_fsync_path()
cleanup_file(path)
val tmp_path = path + ".tmp"
cleanup_file(tmp_path)
atomic_write(path, "test content")
expect(rt_file_exists(tmp_path)).to_equal(false)
cleanup_file(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `7a7283c52305dbacdb8526617d25d9f51c232af480a3df60c3e8c8a1e0e7a01d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a7283c52305dbacdb8526617d25d9f51c232af480a3df60c3e8c8a1e0e7a01d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a7283c52305dbacdb8526617d25d9f51c232af480a3df60c3e8c8a1e0e7a01d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/stdlib/database/atomic_fsync_spec.spl
mirror: doc/06_spec/03_system/stdlib/database/atomic_fsync_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/database/atomic_fsync_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/database/atomic_fsync_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/database/atomic_fsync_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true for an existing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/atomic_fsync_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for nonexistent file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/atomic_fsync_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for invalid path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

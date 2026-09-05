# dbfs_posix_shim_spec

> DBFS POSIX Shim Specification (D10)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_posix_shim_spec

DBFS POSIX Shim Specification (D10)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_posix_shim_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS POSIX Shim Specification (D10)

Verifies the POSIX-compat subset (D10):
  - random write via COW rewrites EXTENT_REF
  - rename-over-existing is atomic
  - unlink-while-open tombstones (data accessible until close)
  - truncate shrink and grow
  - out-of-scope ops return ENOTSUP (mmap shared-writable, hard links, O_DIRECT)

## Scenarios

### DBFS POSIX Shim — random write via COW

#### pwrite at offset rewrites EXTENT_REF; subsequent pread returns new data

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pwrite at offset rewrites EXTENT_REF; subsequent pread returns new data
   - Expected: got equals `AAAAACCCCC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pwrite at offset rewrites EXTENT_REF; subsequent pread returns new data")
val mt = make_mounted()
val fh = mt.open("/data/cow.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "AAAAABBBBB").unwrap()
mt.pwrite(fh, "CCCCC", 5).unwrap()
val fh2 = mt.open("/data/cow.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh2, 10).unwrap()
expect(got).to_equal("AAAAACCCCC")
```

</details>

#### pwrite does not corrupt bytes before the written offset

- pwrite does not corrupt bytes before the written offset
   - Expected: got[0] equals `'X'`
   - Expected: got[8] equals `'Y'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pwrite does not corrupt bytes before the written offset")
val mt = make_mounted()
val fh = mt.open("/data/cow2.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "XXXXXXXXXX").unwrap()
mt.pwrite(fh, "YY", 8).unwrap()
val fh2 = mt.open("/data/cow2.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh2, 10).unwrap()
expect(got[0]).to_equal('X')
expect(got[8]).to_equal('Y')
```

</details>

### DBFS POSIX Shim — rename-over-existing

#### rename-over-existing is atomic (target replaced)

- rename-over-existing is atomic (target replaced)
   - Expected: got equals `aaa`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rename-over-existing is atomic (target replaced)")
val mt = make_mounted()
val fh1 = mt.open("/data/a.txt", OpenFlags.create_write()).unwrap()
mt.write(fh1, "aaa").unwrap()
mt.close(fh1).unwrap()
val fh2 = mt.open("/data/b.txt", OpenFlags.create_write()).unwrap()
mt.write(fh2, "bbb").unwrap()
mt.close(fh2).unwrap()
mt.rename("/data/a.txt", "/data/b.txt").unwrap()
val fh3 = mt.open("/data/b.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh3, 3).unwrap()
expect(got).to_equal("aaa")
```

</details>

### DBFS POSIX Shim — unlink-while-open tombstone

#### unlink while handle open: data accessible until close

- unlink while handle open: data accessible until close
   - Expected: got equals `ghost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unlink while handle open: data accessible until close")
val mt = make_mounted()
val fh = mt.open("/data/tomb.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "ghost").unwrap()
mt.unlink("/data/tomb.txt").unwrap()
# File is unlinked but handle still valid
val got = mt.read(fh, 5).unwrap()
expect(got).to_equal("ghost")
mt.close(fh).unwrap()
```

</details>

#### after close, unlinked file is not accessible

- after close, unlinked file is not accessible
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("after close, unlinked file is not accessible")
val mt = make_mounted()
val fh = mt.open("/data/gone.txt", OpenFlags.create_write()).unwrap()
mt.unlink("/data/gone.txt").unwrap()
mt.close(fh).unwrap()
val r = mt.stat("/data/gone.txt")
expect(r.is_err()).to_equal(true)
```

</details>

### DBFS POSIX Shim — truncate

#### truncate shrinks file; stat shows new size

- truncate shrinks file; stat shows new size
   - Expected: stat.size equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("truncate shrinks file; stat shows new size")
val mt = make_mounted()
val fh = mt.open("/data/trunc.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "0123456789").unwrap()
mt.ftruncate(fh, 5).unwrap()
val stat = mt.stat("/data/trunc.txt").unwrap()
expect(stat.size).to_equal(5)
```

</details>

#### truncate grows file; extended region reads as zeros

- truncate grows file; extended region reads as zeros
   - Expected: got[0] equals `\0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("truncate grows file; extended region reads as zeros")
val mt = make_mounted()
val fh = mt.open("/data/grow.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "AB").unwrap()
mt.ftruncate(fh, 6).unwrap()
val fh2 = mt.open("/data/grow.txt", OpenFlags.read_only()).unwrap()
val got = mt.pread(fh2, 2, 4).unwrap()
expect(got[0]).to_equal("\0")
```

</details>

### DBFS POSIX Shim — out-of-scope ops return ENOTSUP

#### mmap_shared_writable returns ENOTSUP

- mmap_shared_writable returns ENOTSUP
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mmap_shared_writable returns ENOTSUP")
val mt = make_mounted()
val fh = mt.open("/data/mmap.txt", OpenFlags.create_write()).unwrap()
val r = mt.mmap_shared_writable(fh, 0, 4096)
expect(r.is_err()).to_equal(true)
```

</details>

#### link (hard link) returns ENOTSUP

- link (hard link) returns ENOTSUP
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("link (hard link) returns ENOTSUP")
val mt = make_mounted()
val fh = mt.open("/data/src.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
val r = mt.link("/data/src.txt", "/data/lnk.txt")
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c34ba4d88c8893b18571fda08afc4d565885f0ab0b8ab53a9285d8eab9f8aec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c34ba4d88c8893b18571fda08afc4d565885f0ab0b8ab53a9285d8eab9f8aec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c34ba4d88c8893b18571fda08afc4d565885f0ab0b8ab53a9285d8eab9f8aec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/storage/dbfs/dbfs_posix_shim_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_posix_shim_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_posix_shim_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_posix_shim_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_posix_shim_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/dbfs_posix_shim_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pwrite at offset rewrites EXTENT_REF; subsequent pread returns new data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_posix_shim_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pwrite does not corrupt bytes before the written offset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_posix_shim_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rename-over-existing is atomic (target replaced)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

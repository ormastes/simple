# dbfs_driver_spec

> DBFS FsDriver Seam Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_driver_spec

DBFS FsDriver Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_driver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS FsDriver Seam Specification

Verifies DbFsDriver implements the FsDriver trait via MountTable:
  open, read, write, stat, readdir, mkdir, unlink, rename

## Scenarios

### DBFS FsDriver — mkdir and stat

#### mkdir creates directory; stat returns is_dir=true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mkdir creates directory; stat returns is_dir=true
   - Expected: info.is_dir is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mkdir creates directory; stat returns is_dir=true")
val mt = make_mounted()
mt.mkdir("/data/mydir", 0o755).unwrap()
val info = mt.stat("/data/mydir").unwrap()
expect(info.is_dir).to_equal(true)
```

</details>

#### stat on missing path returns error

- stat on missing path returns error
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stat on missing path returns error")
val mt = make_mounted()
val r = mt.stat("/data/ghost")
expect(r.is_err()).to_equal(true)
```

</details>

### DBFS FsDriver — open, write, read

#### open with create_write creates file

- open with create_write creates file
   - Expected: fh.id > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("open with create_write creates file")
val mt = make_mounted()
val fh = mt.open("/data/hello.txt", OpenFlags.create_write()).unwrap()
expect(fh.id > 0).to_equal(true)
```

</details>

#### write then read round-trips content

- write then read round-trips content
   - Expected: got equals `hello dbfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write then read round-trips content")
val mt = make_mounted()
val fh = mt.open("/data/rw.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "hello dbfs").unwrap()
val fh2 = mt.open("/data/rw.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh2, 10).unwrap()
expect(got).to_equal("hello dbfs")
```

</details>

#### read on closed handle returns error

- read on closed handle returns error
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read on closed handle returns error")
val mt = make_mounted()
val fh = mt.open("/data/tmp.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
val r = mt.read(fh, 5)
expect(r.is_err()).to_equal(true)
```

</details>

#### read-only open of a missing file is side-effect free

- read-only open of a missing file is side-effect free
   - Expected: opened.is_err() is true
   - Expected: mt.stat("/data/missing.bin").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read-only open of a missing file is side-effect free")
val mt = make_mounted()
val opened = mt.open("/data/missing.bin", OpenFlags.read_only())
expect(opened.is_err()).to_equal(true)
expect(mt.stat("/data/missing.bin").is_err()).to_equal(true)
```

</details>

#### create-exclusive rejects an existing file without replacing content

- create-exclusive rejects an existing file without replacing content
   - Expected: mt.open("/data/exclusive.bin", exclusive).is_err() is true
   - Expected: mt.read(reopened, 8).unwrap() equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("create-exclusive rejects an existing file without replacing content")
val mt = make_mounted()
val first = mt.open("/data/exclusive.bin", OpenFlags.create_write()).unwrap()
mt.write(first, "original").unwrap()
mt.close(first).unwrap()
val exclusive = OpenFlags.create_write().with_excl()
expect(mt.open("/data/exclusive.bin", exclusive).is_err()).to_equal(true)
val reopened = mt.open("/data/exclusive.bin", OpenFlags.read_only()).unwrap()
expect(mt.read(reopened, 8).unwrap()).to_equal("original")
```

</details>

#### writable truncate-open publishes an empty replacement generation

- writable truncate-open publishes an empty replacement generation
   - Expected: mt.stat("/data/truncate.bin").unwrap().size equals `0`
   - Expected: mt.open("/data/truncate.bin", OpenFlags.read_only().with_trunc()).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writable truncate-open publishes an empty replacement generation")
val mt = make_mounted()
val first = mt.open("/data/truncate.bin", OpenFlags.create_write()).unwrap()
mt.write(first, "old-content").unwrap()
mt.close(first).unwrap()
val truncated = mt.open("/data/truncate.bin", OpenFlags.write_only().with_trunc()).unwrap()
expect(mt.stat("/data/truncate.bin").unwrap().size).to_equal(0)
mt.close(truncated).unwrap()
expect(mt.open("/data/truncate.bin", OpenFlags.read_only().with_trunc()).is_err()).to_equal(true)
```

</details>

### DBFS FsDriver — readdir

#### readdir on mounted dir returns created entries

- readdir on mounted dir returns created entries
   - Expected: entries.len() >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("readdir on mounted dir returns created entries")
val mt = make_mounted()
mt.mkdir("/data/alpha", 0o755).unwrap()
mt.mkdir("/data/beta", 0o755).unwrap()
val dh = mt.opendir("/data").unwrap()
val entries = mt.readdir(dh).unwrap()
expect(entries.len() >= 2).to_equal(true)
```

</details>

### DBFS FsDriver — unlink and rename

#### unlink removes file; stat returns error

- unlink removes file; stat returns error
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unlink removes file; stat returns error")
val mt = make_mounted()
val fh = mt.open("/data/del.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
mt.unlink("/data/del.txt").unwrap()
val r = mt.stat("/data/del.txt")
expect(r.is_err()).to_equal(true)
```

</details>

#### rename moves file; old path gone, new path exists

- rename moves file; old path gone, new path exists
   - Expected: old_r.is_err() is true
   - Expected: new_r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rename moves file; old path gone, new path exists")
val mt = make_mounted()
val fh = mt.open("/data/old.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
mt.rename("/data/old.txt", "/data/new.txt").unwrap()
val old_r = mt.stat("/data/old.txt")
val new_r = mt.stat("/data/new.txt")
expect(old_r.is_err()).to_equal(true)
expect(new_r.is_ok()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `d1a84d39f6fb0345eed0684df28891e177119f423e3469ba46deb7d3c95846e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1a84d39f6fb0345eed0684df28891e177119f423e3469ba46deb7d3c95846e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1a84d39f6fb0345eed0684df28891e177119f423e3469ba46deb7d3c95846e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/storage/dbfs/dbfs_driver_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/dbfs_driver_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/dbfs_driver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/dbfs_driver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/dbfs_driver_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/dbfs/dbfs_driver_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mkdir creates directory; stat returns is_dir=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_driver_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stat on missing path returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_driver_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open with create_write creates file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

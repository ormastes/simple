# dbfs_fs_driver_spec

> DBFS FsDriver Engine Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_fs_driver_spec

DBFS FsDriver Engine Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_fs_driver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS FsDriver Engine Specification

Verifies DbfsFsDriver — the engine-backed driver that wires NsBTree
namespace lookups with arena-backed file data storage:
  1. open creates a file; stat returns is_file=true
  2. write then read round-trips content via arena
  3. readdir lists created files
  4. unlink hides the file from stat
  5. rename moves path and updates NsBTree
  6. mkdir creates directory; stat returns is_dir=true
  7. close + read on closed handle returns error

## Scenarios

### DbfsFsDriver — open and stat

#### open creates file; stat returns is_file=true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- open creates file; stat returns is_file=true
   - Expected: fh.id > 0 is true
   - Expected: info.is_file is true
   - Expected: info.is_dir is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("open creates file; stat returns is_file=true")
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/hello.txt"), OpenFlags.create_write()).unwrap()
expect(fh.id > 0).to_equal(true)
val info = drv.stat_path(Path(raw: "/hello.txt")).unwrap()
expect(info.is_file).to_equal(true)
expect(info.is_dir).to_equal(false)
```

</details>

#### stat on missing path returns NotFound

- stat on missing path returns NotFound
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stat on missing path returns NotFound")
val drv = DbfsFsDriver.new()
val r = drv.stat_path(Path(raw: "/ghost.txt"))
expect(r.is_err()).to_equal(true)
```

</details>

#### stat on root returns is_dir=true

- stat on root returns is_dir=true
   - Expected: info.is_dir is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stat on root returns is_dir=true")
val drv = DbfsFsDriver.new()
val info = drv.stat_path(Path(raw: "/")).unwrap()
expect(info.is_dir).to_equal(true)
```

</details>

### DbfsFsDriver — write and read

#### write then read_handle round-trips content

- write then read_handle round-trips content
   - Expected: got equals `hello dbfs engine`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write then read_handle round-trips content")
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/rw.txt"), OpenFlags.create_write()).unwrap()
drv.write_handle(fh, "hello dbfs engine").unwrap()
val fh2 = drv.open_path(Path(raw: "/rw.txt"), OpenFlags.read_only()).unwrap()
val got = drv.read_handle(fh2, 17).unwrap()
expect(got).to_equal("hello dbfs engine")
```

</details>

#### size after write reflects byte count

- size after write reflects byte count
   - Expected: info.size equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("size after write reflects byte count")
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/sized.txt"), OpenFlags.create_write()).unwrap()
drv.write_handle(fh, "abc").unwrap()
val info = drv.stat_path(Path(raw: "/sized.txt")).unwrap()
expect(info.size).to_equal(3)
```

</details>

#### empty file has size 0

- empty file has size 0
   - Expected: info.size equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("empty file has size 0")
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/empty.txt"), OpenFlags.create_write()).unwrap()
val info = drv.stat_path(Path(raw: "/empty.txt")).unwrap()
expect(info.size).to_equal(0)
```

</details>

### DbfsFsDriver — close

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
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/tmp.txt"), OpenFlags.create_write()).unwrap()
drv.close_handle(fh).unwrap()
val r = drv.read_handle(fh, 5)
expect(r.is_err()).to_equal(true)
```

</details>

#### close on invalid handle returns error

- close on invalid handle returns error
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("close on invalid handle returns error")
val drv = DbfsFsDriver.new()
val bad = FileHandle(id: 9999u64)
val r = drv.close_handle(bad)
expect(r.is_err()).to_equal(true)
```

</details>

### DbfsFsDriver — namespace via NsBTree

#### readdir lists all created files

- readdir lists all created files
   - Expected: entries.len() >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("readdir lists all created files")
val drv = DbfsFsDriver.new()
drv.open_path(Path(raw: "/a.txt"), OpenFlags.create_write()).unwrap()
drv.open_path(Path(raw: "/b.txt"), OpenFlags.create_write()).unwrap()
val dh = drv.opendir_path(Path(raw: "/")).unwrap()
val entries = drv.readdir_handle(dh).unwrap()
expect(entries.len() >= 2).to_equal(true)
```

</details>

#### unlink hides file from stat

- unlink hides file from stat
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unlink hides file from stat")
val drv = DbfsFsDriver.new()
drv.open_path(Path(raw: "/bye.txt"), OpenFlags.create_write()).unwrap()
drv.unlink_path("/bye.txt").unwrap()
val r = drv.stat_path(Path(raw: "/bye.txt"))
expect(r.is_err()).to_equal(true)
```

</details>

#### rename moves file to new path

- rename moves file to new path
   - Expected: r_old.is_err() is true
   - Expected: r_new.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rename moves file to new path")
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/old.txt"), OpenFlags.create_write()).unwrap()
drv.write_handle(fh, "data").unwrap()
drv.rename_path("/old.txt", "/new.txt").unwrap()
val r_old = drv.stat_path(Path(raw: "/old.txt"))
expect(r_old.is_err()).to_equal(true)
val r_new = drv.stat_path(Path(raw: "/new.txt"))
expect(r_new.is_ok()).to_equal(true)
```

</details>

### DbfsFsDriver — mkdir

#### mkdir creates directory; stat returns is_dir=true

- mkdir creates directory; stat returns is_dir=true
   - Expected: info.is_dir is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mkdir creates directory; stat returns is_dir=true")
val drv = DbfsFsDriver.new()
drv.mkdir_path("/mydir", 0o755).unwrap()
val info = drv.stat_path(Path(raw: "/mydir")).unwrap()
expect(info.is_dir).to_equal(true)
```

</details>

#### mkdir twice returns AlreadyExists

- mkdir twice returns AlreadyExists
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mkdir twice returns AlreadyExists")
val drv = DbfsFsDriver.new()
drv.mkdir_path("/dup", 0o755).unwrap()
val r = drv.mkdir_path("/dup", 0o755)
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `d9c0c8de4957d537c36104f3ece51df6fb1aa4b74e04cd2bd1db52512e3b0fef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d9c0c8de4957d537c36104f3ece51df6fb1aa4b74e04cd2bd1db52512e3b0fef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d9c0c8de4957d537c36104f3ece51df6fb1aa4b74e04cd2bd1db52512e3b0fef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/storage/dbfs/dbfs_fs_driver_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_fs_driver_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_fs_driver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_fs_driver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_fs_driver_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/dbfs_fs_driver_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open creates file; stat returns is_file=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_fs_driver_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stat on missing path returns NotFound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_fs_driver_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stat on root returns is_dir=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

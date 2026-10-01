# FAT32 kernel rename primitive (`Fat32Filesystem.rename_at`)

> `os.kernel.ipc.syscall_file`'s `_handle_file_rename` previously returned

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 kernel rename primitive (`Fat32Filesystem.rename_at`)

`os.kernel.ipc.syscall_file`'s `_handle_file_rename` previously returned

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/fat32_rename_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`os.kernel.ipc.syscall_file`'s `_handle_file_rename` previously returned
`-ENOSYS` unconditionally (see
`doc/08_tracking/bug/path_based_fs_syscalls_fake_success_2026-08-06.md`).
This spec proves the new `Fat32Filesystem.rename_at` primitive it now calls
is real: it moves a directory entry (name + parent, never the file's DATA)
by linking a new entry (reusing `_link_entry`'s tested LFN/8.3 machinery)
and then marking the old entry deleted (`_mark_dirent_deleted`).

**Why this spec, not `_handle_file_rename` directly:** the sibling spec
`fat32_mount_and_dir_ops_spec.spl` already recorded that exercising
`_handle_file_*` handlers directly hits a pre-existing seed/harness
limitation — importing the full scheduler/vmm/pmm/ipc/syscall graph makes
the currently-deployed bootstrap-seed `bin/simple` report
"no examples executed" even for an existing, unmodified spec
(`syscall_spec.spl`). That is a harness limitation, not something this
change can fix, so — same choice `fat32_mount_and_dir_ops_spec.spl` made —
this spec drives `Fat32Filesystem.rename_at` directly (the same real
primitive `_handle_file_rename` calls with the caller's path already
resolved) and additionally content-verifies through `read`/`write`, proving
the renamed entry's DATA — not just its directory-entry metadata — survives
intact.

**Anti-false-green measure:** every post-rename assertion (old name gone,
new name present with the SAME content and start_cluster, EEXIST on
overwrite) re-reads through a FRESH `Fat32Filesystem` view built from the
mutated mock device, never through the object that performed the rename —
the same discipline `fat32_write_path_spec.spl` and
`fat32_mount_and_dir_ops_spec.spl` established.

## Scenarios

### Fat32Filesystem.rename_at — same-directory rename

#### renames a file in place: new name reads the same content, old name is gone

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renames a file in place: new name reads the same content, old name is gone
- create /OLD.TXT with real content and write it through open+write
- rename /OLD.TXT -> /NEW.TXT through a FRESH view
- re-read through ANOTHER fresh view: old name gone, new name present with same content
   - Expected: old_stat.unwrap_err() equals `-2)   # ENOENT`
- data untouched: same start_cluster, proving only the dirent moved
   - Expected: handle.start_cluster equals `before_cluster`
   - Expected: _text_of(buf) equals `hello rename`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("renames a file in place: new name reads the same content, old name is gone")
val dev = _make_dev()
var fs = _fs_from(dev)
step("create /OLD.TXT with real content and write it through open+write")
assert_true(fs.create_at(dev, "/OLD.TXT").is_ok())
val h0 = fs.open_at(dev, "/OLD.TXT")
assert_true(h0.is_ok())
val wr = fs.write(dev, h0.unwrap(), _bytes("hello rename"))
assert_true(wr.is_ok())
val before_cluster = wr.unwrap().start_cluster

step("rename /OLD.TXT -> /NEW.TXT through a FRESH view")
val fs1 = _fs_from(dev)
val rn = fs1.rename_at(dev, "/OLD.TXT", "/NEW.TXT")
assert_true(rn.is_ok())

step("re-read through ANOTHER fresh view: old name gone, new name present with same content")
val fs2 = _fs_from(dev)
val old_stat = fs2.stat_at(dev, "/OLD.TXT")
assert_true(old_stat.is_err())
expect(old_stat.unwrap_err()).to_equal(-2)   # ENOENT

val new_open = fs2.open_at(dev, "/NEW.TXT")
assert_true(new_open.is_ok())
val handle = new_open.unwrap()
step("data untouched: same start_cluster, proving only the dirent moved")
expect(handle.start_cluster).to_equal(before_cluster)
val buf: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
val rd = fs2.read(dev, handle, buf)
assert_true(rd.is_ok())
expect(_text_of(buf)).to_equal("hello rename")
```

</details>

#### returns EEXIST rather than silently overwriting an existing destination

- returns EEXIST rather than silently overwriting an existing destination
   - Expected: rn.unwrap_err() equals `-17)   # EEXIST — no atomic replace, by design`
- both original files are untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns EEXIST rather than silently overwriting an existing destination")
val dev = _make_dev()
var fs = _fs_from(dev)
assert_true(fs.create_at(dev, "/A.TXT").is_ok())
assert_true(fs.create_at(dev, "/B.TXT").is_ok())
val fs2 = _fs_from(dev)
val rn = fs2.rename_at(dev, "/A.TXT", "/B.TXT")
assert_true(rn.is_err())
expect(rn.unwrap_err()).to_equal(-17)   # EEXIST — no atomic replace, by design
step("both original files are untouched")
val fs3 = _fs_from(dev)
assert_true(fs3.stat_at(dev, "/A.TXT").is_ok())
assert_true(fs3.stat_at(dev, "/B.TXT").is_ok())
```

</details>

### Fat32Filesystem.rename_at — cross-directory move

#### moves a file into a subdirectory: content preserved, gone from the old parent

- moves a file into a subdirectory: content preserved, gone from the old parent
- rename /SRC.TXT -> /DEST/SRC.TXT through a FRESH view
   - Expected: _text_of(buf) equals `cross dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("moves a file into a subdirectory: content preserved, gone from the old parent")
val dev = _make_dev()
var fs = _fs_from(dev)
assert_true(fs.mkdir_at(dev, "/DEST").is_ok())
assert_true(fs.create_at(dev, "/SRC.TXT").is_ok())
val h0 = fs.open_at(dev, "/SRC.TXT")
assert_true(h0.is_ok())
assert_true(fs.write(dev, h0.unwrap(), _bytes("cross dir")).is_ok())

step("rename /SRC.TXT -> /DEST/SRC.TXT through a FRESH view")
val fs1 = _fs_from(dev)
val rn = fs1.rename_at(dev, "/SRC.TXT", "/DEST/SRC.TXT")
assert_true(rn.is_ok())

val fs2 = _fs_from(dev)
val old_stat = fs2.stat_at(dev, "/SRC.TXT")
assert_true(old_stat.is_err())
val moved = fs2.open_at(dev, "/DEST/SRC.TXT")
assert_true(moved.is_ok())
val buf: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
val rd = fs2.read(dev, moved.unwrap(), buf)
assert_true(rd.is_ok())
expect(_text_of(buf)).to_equal("cross dir")
```

</details>

#### moving a directory patches its own '..' entry to the new parent

- moving a directory patches its own '..' entry to the new parent
- moved directory is readable at its new path
- '..' from inside the moved directory now resolves through /DEST
- old location is gone


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("moving a directory patches its own '..' entry to the new parent")
val dev = _make_dev()
var fs = _fs_from(dev)
assert_true(fs.mkdir_at(dev, "/DEST").is_ok())
assert_true(fs.mkdir_at(dev, "/CHILD").is_ok())
val fs1 = _fs_from(dev)
val rn = fs1.rename_at(dev, "/CHILD", "/DEST/CHILD")
assert_true(rn.is_ok())

val fs2 = _fs_from(dev)
step("moved directory is readable at its new path")
val moved_names = fs2.readdir_at(dev, "/DEST/CHILD")
assert_true(moved_names.is_ok())
step("'..' from inside the moved directory now resolves through /DEST")
val via_dotdot = fs2.stat_at(dev, "/DEST/CHILD/../CHILD")
assert_true(via_dotdot.is_ok())
step("old location is gone")
val gone = fs2.stat_at(dev, "/CHILD")
assert_true(gone.is_err())
```

</details>

#### rejects moving a directory into itself with EINVAL

- rejects moving a directory into itself with EINVAL
   - Expected: rn.unwrap_err() equals `-22)   # EINVAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects moving a directory into itself with EINVAL")
val dev = _make_dev()
var fs = _fs_from(dev)
assert_true(fs.mkdir_at(dev, "/SELF").is_ok())
val fs2 = _fs_from(dev)
val rn = fs2.rename_at(dev, "/SELF", "/SELF/SELF")
assert_true(rn.is_err())
expect(rn.unwrap_err()).to_equal(-22)   # EINVAL
```

</details>

### Fat32Filesystem.rename_at — old entry actually removed, not just aliased

#### after rename the OLD name is gone AND the directory shows exactly one live entry for it

- after rename the OLD name is gone AND the directory shows exactly one live entry for it
- exactly one live entry in root — not two, proving the old dirent was really deleted, not just shadowed
   - Expected: names.unwrap().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("after rename the OLD name is gone AND the directory shows exactly one live entry for it")
val dev = _make_dev()
var fs = _fs_from(dev)
assert_true(fs.create_at(dev, "/KEEP.TXT").is_ok())
val fs1 = _fs_from(dev)
assert_true(fs1.rename_at(dev, "/KEEP.TXT", "/KEPT.TXT").is_ok())
val fs2 = _fs_from(dev)
assert_true(fs2.stat_at(dev, "/KEEP.TXT").is_err())
assert_true(fs2.stat_at(dev, "/KEPT.TXT").is_ok())
step("exactly one live entry in root — not two, proving the old dirent was really deleted, not just shadowed")
val names = fs2.readdir_at(dev, "/")
assert_true(names.is_ok())
expect(names.unwrap().len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6da8c023a2e153b283b2bc5d746e8d043c068004dcb71a31cc3c299847cea5cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6da8c023a2e153b283b2bc5d746e8d043c068004dcb71a31cc3c299847cea5cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6da8c023a2e153b283b2bc5d746e8d043c068004dcb71a31cc3c299847cea5cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/kernel/fs/fat32_rename_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/fs/fat32_rename_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/fs/fat32_rename_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/fs/fat32_rename_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/fs/fat32_rename_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/fs/fat32_rename_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renames a file in place: new name reads the same content, old name is gone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_rename_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns EEXIST rather than silently overwriting an existing destination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_rename_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves a file into a subdirectory: content preserved, gone from the old parent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

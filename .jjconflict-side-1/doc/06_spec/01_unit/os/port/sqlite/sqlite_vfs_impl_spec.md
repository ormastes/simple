# @manual: primary

> Purpose: Prove that SQLite VFS impl — file IO carries real bytes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that SQLite VFS impl — file IO carries real bytes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SQLite VFS impl — file IO carries real bytes.
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

### SQLite VFS impl — file IO carries real bytes

#### read-after-write returns exactly the bytes written

- Verify: read-after-write returns exactly the bytes written
   - Expected: h equals `0`
   - Expected: v.x_write(h, 0, bytes_from_text("SQLite format 3")) equals `sqlite_ok()`
   - Expected: rr.code equals `sqlite_ok()`
   - Expected: bytes_equal(rr.data, bytes_from_text("SQLite format 3")) is true
   - Expected: bytes_equal(read_all_bytes(base), bytes_from_text("SQLite format 3")) is true
   - Expected: v.x_close(h) equals `sqlite_ok()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: read-after-write returns exactly the bytes written")
val base = tpath("rw")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
expect(h).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(v.x_write(h, 0, bytes_from_text("SQLite format 3"))).to_equal(sqlite_ok())
val rr = v.x_read(h, 0, 15)
expect(rr.code).to_equal(sqlite_ok())
expect(bytes_equal(rr.data, bytes_from_text("SQLite format 3"))).to_equal(true)
# And the bytes are really on the filesystem, not just in the VFS.
expect(bytes_equal(read_all_bytes(base), bytes_from_text("SQLite format 3"))).to_equal(true)
expect(v.x_close(h)).to_equal(sqlite_ok())
clean(base)
```

</details>

#### an offset write lands at the offset and leaves the prefix intact

- Verify: an offset write lands at the offset and leaves the prefix intact
   - Expected: v.x_write(h, 4, bytes_from_text("ZZZZ")) equals `sqlite_ok()`
   - Expected: rr.code equals `sqlite_ok()`
   - Expected: bytes_equal(rr.data, bytes_from_text("AAAAZZZZ")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: an offset write lands at the offset and leaves the prefix intact")
val base = tpath("off")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_write(h, 0, bytes_from_text("AAAABBBB"))
expect(v.x_write(h, 4, bytes_from_text("ZZZZ"))).to_equal(sqlite_ok())
val rr = v.x_read(h, 0, 8)
expect(rr.code).to_equal(sqlite_ok())
expect(bytes_equal(rr.data, bytes_from_text("AAAAZZZZ"))).to_equal(true)
v.x_close(h)
clean(base)
```

</details>

#### a write past EOF zero-fills the hole, like pwrite

- Verify: a write past EOF zero-fills the hole, like pwrite
   - Expected: v.x_write(h, 5, bytes_from_text("Z")) equals `sqlite_ok()`
   - Expected: sr.code equals `sqlite_ok()`
   - Expected: sr.size equals `6`
   - Expected: rr.code equals `sqlite_ok()`
   - Expected: rr.data[2] equals `0`
   - Expected: rr.data[3] equals `0`
   - Expected: rr.data[4] equals `0`
   - Expected: rr.data[5] equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: a write past EOF zero-fills the hole, like pwrite")
val base = tpath("hole")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_write(h, 0, bytes_from_text("AB"))
expect(v.x_write(h, 5, bytes_from_text("Z"))).to_equal(sqlite_ok())
val sr = v.x_file_size(h)
expect(sr.code).to_equal(sqlite_ok())
expect(sr.size).to_equal(6)  # oracle: 6 — named expected value from the requirement
val rr = v.x_read(h, 0, 6)
expect(rr.code).to_equal(sqlite_ok())
expect(rr.data[2]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(rr.data[3]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(rr.data[4]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(rr.data[5]).to_equal(90)  # oracle: 90 — named expected value from the requirement
v.x_close(h)
clean(base)
```

</details>

#### a short read zero-fills the tail and returns SQLITE_IOERR_SHORT_READ

- Verify: a short read zero-fills the tail and returns SQLITE_IOERR_SHORT_READ
   - Expected: rr.code equals `sqlite_ioerr_short_read()`
   - Expected: rr.data.len() equals `8`
   - Expected: rr.data[0] equals `67`
   - Expected: rr.data[1] equals `68`
   - Expected: rr.data[2] equals `0`
   - Expected: rr.data[7] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: a short read zero-fills the tail and returns SQLITE_IOERR_SHORT_READ")
val base = tpath("short")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_write(h, 0, bytes_from_text("ABCD"))
val rr = v.x_read(h, 2, 8)
expect(rr.code).to_equal(sqlite_ioerr_short_read())
expect(rr.data.len()).to_equal(8)  # oracle: 8 — named expected value from the requirement
expect(rr.data[0]).to_equal(67)  # oracle: 67 — named expected value from the requirement
expect(rr.data[1]).to_equal(68)  # oracle: 68 — named expected value from the requirement
expect(rr.data[2]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(rr.data[7]).to_equal(0)  # oracle: 0 — named expected value from the requirement
v.x_close(h)
clean(base)
```

</details>

#### xFileSize reports the real on-disk size

- Verify: xFileSize reports the real on-disk size
   - Expected: sr.code equals `sqlite_ok()`
   - Expected: sr.size equals `300`
   - Expected: rt_file_size(base) equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xFileSize reports the real on-disk size")
val base = tpath("size")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_write(h, 0, filled_bytes(300, 7))
val sr = v.x_file_size(h)
expect(sr.code).to_equal(sqlite_ok())
expect(sr.size).to_equal(300)  # oracle: 300 — named expected value from the requirement
expect(rt_file_size(base)).to_equal(300)  # oracle: 300 — named expected value from the requirement
v.x_close(h)
clean(base)
```

</details>

### SQLite VFS impl — xTruncate uses the house atomic pattern

#### truncate shrinks to exactly the requested size and keeps the prefix

- Verify: truncate shrinks to exactly the requested size and keeps the prefix
   - Expected: v.x_truncate(h, 4) equals `sqlite_ok()`
   - Expected: sr.size equals `4`
   - Expected: rt_file_size(base) equals `4`
   - Expected: rr.code equals `sqlite_ok()`
   - Expected: bytes_equal(rr.data, bytes_from_text("0123")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: truncate shrinks to exactly the requested size and keeps the prefix")
val base = tpath("trunc")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_write(h, 0, bytes_from_text("0123456789"))
expect(v.x_truncate(h, 4)).to_equal(sqlite_ok())
val sr = v.x_file_size(h)
expect(sr.size).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(rt_file_size(base)).to_equal(4)  # oracle: 4 — named expected value from the requirement
val rr = v.x_read(h, 0, 4)
expect(rr.code).to_equal(sqlite_ok())
expect(bytes_equal(rr.data, bytes_from_text("0123"))).to_equal(true)
v.x_close(h)
clean(base)
```

</details>

#### truncate to zero empties the file and leaves no .tmp behind

- Verify: truncate to zero empties the file and leaves no .tmp behind
   - Expected: v.x_truncate(h, 0) equals `sqlite_ok()`
   - Expected: rt_file_size(base) equals `0`
   - Expected: rt_file_exists(base + ".sqlvfs.tmp") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: truncate to zero empties the file and leaves no .tmp behind")
val base = tpath("trunc0")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_write(h, 0, bytes_from_text("payload"))
expect(v.x_truncate(h, 0)).to_equal(sqlite_ok())
expect(rt_file_size(base)).to_equal(0)  # oracle: 0 — named expected value from the requirement
# The tmp was renamed, not left as litter — that is the whole point of
# the tmp+fsync+rename pattern.
expect(rt_file_exists(base + ".sqlvfs.tmp")).to_equal(false)
v.x_close(h)
clean(base)
```

</details>

#### a negative truncate is rejected with SQLITE_IOERR_TRUNCATE

- Verify: a negative truncate is rejected with SQLITE_IOERR_TRUNCATE
   - Expected: v.x_truncate(h, -1) equals `sqlite_ioerr_truncate()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: a negative truncate is rejected with SQLITE_IOERR_TRUNCATE")
val base = tpath("truncneg")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
expect(v.x_truncate(h, -1)).to_equal(sqlite_ioerr_truncate())
v.x_close(h)
clean(base)
```

</details>

### SQLite VFS impl — rollback-journal durability ordering

#### the correct sequence lands and the journal is DURABLE ON DISK before the page write

- Verify: the correct sequence lands and the journal is DURABLE ON DISK before the page write
   - Expected: v.x_write(hj, 0, bytes_from_text("OLDPAGE.")) equals `sqlite_ok()`
   - Expected: v.x_sync(hj, sync_full()) equals `sqlite_ok()`
   - Expected: bytes_equal(read_all_bytes(journal_path_for(base)), bytes_from_text("OLDPAGE.")) is true
   - Expected: bytes_equal(read_all_bytes(base), bytes_from_text("OLDPAGE.")) is true
   - Expected: v.x_write(hdb, 0, bytes_from_text("NEWPAGE!")) equals `sqlite_ok()`
   - Expected: v.x_sync(hdb, sync_full()) equals `sqlite_ok()`
   - Expected: bytes_equal(read_all_bytes(base), bytes_from_text("NEWPAGE!")) is true
   - Expected: v.x_delete(journal_path_for(base), true) equals `sqlite_ok()`
   - Expected: rt_file_exists(journal_path_for(base)) is false
   - Expected: v.journal_before_page_ordering_holds(base) is true
   - Expected: v.violation_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: the correct sequence lands and the journal is DURABLE ON DISK before the page write")
val base = tpath("ord_ok")
clean(base)
var v = new_vfs()
val hdb = v.x_open(base, db_flags())
val hj = v.x_open(journal_path_for(base), journal_flags())

# 1. the database page as it exists today
v.x_write(hdb, 0, bytes_from_text("OLDPAGE."))
v.x_sync(hdb, sync_full())

# 2. journal the PRE-IMAGE of the page we are about to modify
expect(v.x_write(hj, 0, bytes_from_text("OLDPAGE."))).to_equal(sqlite_ok())

# 3. make the journal durable
expect(v.x_sync(hj, sync_full())).to_equal(sqlite_ok())

# CRASH POINT: right here, before the page is touched, the pre-image
# must already be readable off the real filesystem. If a power cut
# happened now, recovery has everything it needs.
expect(bytes_equal(read_all_bytes(journal_path_for(base)), bytes_from_text("OLDPAGE."))).to_equal(true)
expect(bytes_equal(read_all_bytes(base), bytes_from_text("OLDPAGE."))).to_equal(true)

# 4. only now overwrite the page
expect(v.x_write(hdb, 0, bytes_from_text("NEWPAGE!"))).to_equal(sqlite_ok())
expect(v.x_sync(hdb, sync_full())).to_equal(sqlite_ok())
expect(bytes_equal(read_all_bytes(base), bytes_from_text("NEWPAGE!"))).to_equal(true)

# 5. commit point: the journal is deleted with a durable directory entry
expect(v.x_delete(journal_path_for(base), true)).to_equal(sqlite_ok())
expect(rt_file_exists(journal_path_for(base))).to_equal(false)

expect(v.journal_before_page_ordering_holds(base)).to_equal(true)
expect(v.violation_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
v.x_close(hdb)
v.x_close(hj)
clean(base)
```

</details>

#### REFUSES a page write while the journal still has unsynced bytes

- Verify: REFUSES a page write while the journal still has unsynced bytes
   - Expected: v.x_write(hj, 0, bytes_from_text("OLDPAGE.")) equals `sqlite_ok()`
   - Expected: v.x_write(hdb, 0, bytes_from_text("NEWPAGE!")) equals `sqlite_ioerr()`
   - Expected: bytes_equal(read_all_bytes(base), bytes_from_text("OLDPAGE.")) is true
   - Expected: v.violation_count() equals `1`
   - Expected: v.x_sync(hj, sync_full()) equals `sqlite_ok()`
   - Expected: v.x_write(hdb, 0, bytes_from_text("NEWPAGE!")) equals `sqlite_ok()`
   - Expected: bytes_equal(read_all_bytes(base), bytes_from_text("NEWPAGE!")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: REFUSES a page write while the journal still has unsynced bytes")
val base = tpath("ord_bad")
clean(base)
var v = new_vfs()
val hdb = v.x_open(base, db_flags())
val hj = v.x_open(journal_path_for(base), journal_flags())

v.x_write(hdb, 0, bytes_from_text("OLDPAGE."))
v.x_sync(hdb, sync_full())

# journal written but DELIBERATELY not synced
expect(v.x_write(hj, 0, bytes_from_text("OLDPAGE."))).to_equal(sqlite_ok())

# the page overwrite must fail closed
expect(v.x_write(hdb, 0, bytes_from_text("NEWPAGE!"))).to_equal(sqlite_ioerr())

# and the database on disk must be UNCHANGED — the refusal is real,
# not cosmetic
expect(bytes_equal(read_all_bytes(base), bytes_from_text("OLDPAGE."))).to_equal(true)
expect(v.violation_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement

# after the journal IS synced, the same write is accepted
expect(v.x_sync(hj, sync_full())).to_equal(sqlite_ok())
expect(v.x_write(hdb, 0, bytes_from_text("NEWPAGE!"))).to_equal(sqlite_ok())
expect(bytes_equal(read_all_bytes(base), bytes_from_text("NEWPAGE!"))).to_equal(true)
v.x_close(hdb)
v.x_close(hj)
clean(base)
```

</details>

#### the log-based ordering verdict independently agrees with the guard

- Verify: the log-based ordering verdict independently agrees with the guard
   - Expected: v.journal_before_page_ordering_holds(base) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: the log-based ordering verdict independently agrees with the guard")
val base = tpath("ord_log")
clean(base)
var v = new_vfs()
val hdb = v.x_open(base, db_flags())
val hj = v.x_open(journal_path_for(base), journal_flags())
v.x_write(hj, 0, bytes_from_text("pre"))
v.x_sync(hj, sync_normal())
v.x_write(hdb, 0, bytes_from_text("new"))
expect(v.journal_before_page_ordering_holds(base)).to_equal(true)
v.x_close(hdb)
v.x_close(hj)
clean(base)
```

</details>

#### CALIBRATION: with the ordering guard dropped, the page write succeeds and the log verdict goes FALSE

- Verify: CALIBRATION: with the ordering guard dropped, the page write succeeds and the log verdict goes FALSE
   - Expected: v.x_write(hdb, 0, bytes_from_text("NEWPAGE!")) equals `sqlite_ok()`
   - Expected: bytes_equal(read_all_bytes(base), bytes_from_text("NEWPAGE!")) is true
   - Expected: v.violation_count() equals `0`
   - Expected: v.journal_before_page_ordering_holds(base) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: CALIBRATION: with the ordering guard dropped, the page write succeeds and the log verdict goes FALSE")
val base = tpath("ord_cal")
clean(base)
var v = new_vfs()
v.enforce_journal_sync_before_page_write = false
val hdb = v.x_open(base, db_flags())
val hj = v.x_open(journal_path_for(base), journal_flags())

v.x_write(hdb, 0, bytes_from_text("OLDPAGE."))
v.x_sync(hdb, sync_full())
v.x_write(hj, 0, bytes_from_text("OLDPAGE."))
# no journal sync — with the guard off this is now ACCEPTED
expect(v.x_write(hdb, 0, bytes_from_text("NEWPAGE!"))).to_equal(sqlite_ok())
# the database has moved on while its recovery source may not be durable
expect(bytes_equal(read_all_bytes(base), bytes_from_text("NEWPAGE!"))).to_equal(true)
# no violation was recorded, because the guard that records them is off
expect(v.violation_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
# but the independent log verdict catches it
expect(v.journal_before_page_ordering_holds(base)).to_equal(false)
v.x_close(hdb)
v.x_close(hj)
clean(base)
```

</details>

#### xSync FULL also fsyncs the parent directory

- Verify: xSync FULL also fsyncs the parent directory
   - Expected: v.x_sync(h, sync_full()) equals `sqlite_ok()`
   - Expected: parent_dir_of(base) equals `scratch_dir()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xSync FULL also fsyncs the parent directory")
val base = tpath("syncdir")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_write(h, 0, bytes_from_text("d"))
expect(v.x_sync(h, sync_full())).to_equal(sqlite_ok())
expect(parent_dir_of(base)).to_equal(scratch_dir())
v.x_close(h)
clean(base)
```

</details>

### SQLite VFS impl — locking over the one existing primitive

#### acquire, conflict, release: a second handle gets SQLITE_BUSY and then succeeds

- Verify: acquire, conflict, release: a second handle gets SQLITE_BUSY and then succeeds
   - Expected: v.x_lock(h1, lock_shared()) equals `sqlite_ok()`
   - Expected: rt_file_exists(base + ".lock") is true
   - Expected: v.x_lock(h2, lock_shared()) equals `sqlite_busy()`
   - Expected: v.x_lock(h1, lock_exclusive()) equals `sqlite_ok()`
   - Expected: v.handle_lock_level(h1) equals `lock_exclusive()`
   - Expected: v.x_unlock(h1, lock_none()) equals `sqlite_ok()`
   - Expected: rt_file_exists(base + ".lock") is false
   - Expected: v.x_lock(h2, lock_shared()) equals `sqlite_ok()`
   - Expected: v.x_unlock(h2, lock_none()) equals `sqlite_ok()`
   - Expected: rt_file_exists(base + ".lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: acquire, conflict, release: a second handle gets SQLITE_BUSY and then succeeds")
val base = tpath("lock")
clean(base)
var v = new_vfs()
val h1 = v.x_open(base, db_flags())
val h2 = v.x_open(base, db_flags())

expect(v.x_lock(h1, lock_shared())).to_equal(sqlite_ok())
expect(rt_file_exists(base + ".lock")).to_equal(true)

# conflicting acquisition fails CLOSED, it does not block or succeed
expect(v.x_lock(h2, lock_shared())).to_equal(sqlite_busy())

# escalation on the holder is fine
expect(v.x_lock(h1, lock_exclusive())).to_equal(sqlite_ok())
expect(v.handle_lock_level(h1)).to_equal(lock_exclusive())

expect(v.x_unlock(h1, lock_none())).to_equal(sqlite_ok())
expect(rt_file_exists(base + ".lock")).to_equal(false)

# now the other handle can take it
expect(v.x_lock(h2, lock_shared())).to_equal(sqlite_ok())
expect(v.x_unlock(h2, lock_none())).to_equal(sqlite_ok())
expect(rt_file_exists(base + ".lock")).to_equal(false)
v.x_close(h1)
v.x_close(h2)
clean(base)
```

</details>

#### the lock is the REAL on-disk FileLock: a separate VFS instance is blocked by it

- Verify: the lock is the REAL on-disk FileLock: a separate VFS instance is blocked by it
   - Expected: a.x_lock(ha, lock_reserved()) equals `sqlite_ok()`
   - Expected: b.x_lock(hb, lock_shared()) equals `sqlite_busy()`
   - Expected: a.x_unlock(ha, lock_none()) equals `sqlite_ok()`
   - Expected: b.x_lock(hb, lock_shared()) equals `sqlite_ok()`
   - Expected: b.x_unlock(hb, lock_none()) equals `sqlite_ok()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: the lock is the REAL on-disk FileLock: a separate VFS instance is blocked by it")
val base = tpath("lock2")
clean(base)
var a = new_vfs()
var b = new_vfs()
val ha = a.x_open(base, db_flags())
val hb = b.x_open(base, db_flags())
expect(a.x_lock(ha, lock_reserved())).to_equal(sqlite_ok())
# `b` shares no in-process table with `a`; it can only see the lockfile.
expect(b.x_lock(hb, lock_shared())).to_equal(sqlite_busy())
expect(a.x_unlock(ha, lock_none())).to_equal(sqlite_ok())
expect(b.x_lock(hb, lock_shared())).to_equal(sqlite_ok())
expect(b.x_unlock(hb, lock_none())).to_equal(sqlite_ok())
a.x_close(ha)
b.x_close(hb)
clean(base)
```

</details>

#### xCheckReservedLock sees another holder and does not see itself

- Verify: xCheckReservedLock sees another holder and does not see itself
   - Expected: before.code equals `sqlite_ok()`
   - Expected: before.value is false
   - Expected: other.code equals `sqlite_ok()`
   - Expected: other.value is true
   - Expected: mine.value is false
   - Expected: after.value is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xCheckReservedLock sees another holder and does not see itself")
val base = tpath("chkres")
clean(base)
var v = new_vfs()
val h1 = v.x_open(base, db_flags())
val h2 = v.x_open(base, db_flags())
val before = v.x_check_reserved_lock(h2)
expect(before.code).to_equal(sqlite_ok())
expect(before.value).to_equal(false)
v.x_lock(h1, lock_reserved())
val other = v.x_check_reserved_lock(h2)
expect(other.code).to_equal(sqlite_ok())
expect(other.value).to_equal(true)
# the holder itself is not "someone else"
val mine = v.x_check_reserved_lock(h1)
expect(mine.value).to_equal(false)
v.x_unlock(h1, lock_none())
val after = v.x_check_reserved_lock(h2)
expect(after.value).to_equal(false)
v.x_close(h1)
v.x_close(h2)
clean(base)
```

</details>

#### xClose releases a still-held lock rather than leaking the lockfile

- Verify: xClose releases a still-held lock rather than leaking the lockfile
   - Expected: rt_file_exists(base + ".lock") is true
   - Expected: v.x_close(h) equals `sqlite_ok()`
   - Expected: rt_file_exists(base + ".lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xClose releases a still-held lock rather than leaking the lockfile")
val base = tpath("lockclose")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_lock(h, lock_exclusive())
expect(rt_file_exists(base + ".lock")).to_equal(true)
expect(v.x_close(h)).to_equal(sqlite_ok())
expect(rt_file_exists(base + ".lock")).to_equal(false)
clean(base)
```

</details>

#### the lock ladder names match sqlite3.h

- Verify: the lock ladder names match sqlite3.h
   - Expected: lock_level_name_of(0) equals `NONE`
   - Expected: lock_level_name_of(1) equals `SHARED`
   - Expected: lock_level_name_of(2) equals `RESERVED`
   - Expected: lock_level_name_of(3) equals `PENDING`
   - Expected: lock_level_name_of(4) equals `EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: the lock ladder names match sqlite3.h")
expect(lock_level_name_of(0)).to_equal("NONE")
expect(lock_level_name_of(1)).to_equal("SHARED")
expect(lock_level_name_of(2)).to_equal("RESERVED")
expect(lock_level_name_of(3)).to_equal("PENDING")
expect(lock_level_name_of(4)).to_equal("EXCLUSIVE")
```

</details>

### SQLite VFS impl — namespace methods

#### xAccess is false for a missing file and true once it exists

- Verify: xAccess is false for a missing file and true once it exists
   - Expected: miss.code equals `sqlite_ok()`
   - Expected: miss.value is false
   - Expected: v.x_access(base, access_read()).value is false
   - Expected: v.x_access(base, access_readwrite()).value is false
   - Expected: hit.code equals `sqlite_ok()`
   - Expected: hit.value is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xAccess is false for a missing file and true once it exists")
val base = tpath("access")
clean(base)
var v = new_vfs()
val miss = v.x_access(base, access_exists())
expect(miss.code).to_equal(sqlite_ok())
expect(miss.value).to_equal(false)
expect(v.x_access(base, access_read()).value).to_equal(false)
expect(v.x_access(base, access_readwrite()).value).to_equal(false)
val h = v.x_open(base, db_flags())
val hit = v.x_access(base, access_exists())
expect(hit.code).to_equal(sqlite_ok())
expect(hit.value).to_equal(true)
v.x_close(h)
clean(base)
```

</details>

#### xOpen without CREATE refuses a missing file

- Verify: xOpen without CREATE refuses a missing file
   - Expected: v.x_open(base, open_main_db() + open_readwrite()) equals `-1`
   - Expected: rt_file_exists(base) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xOpen without CREATE refuses a missing file")
val base = tpath("nocreate")
clean(base)
var v = new_vfs()
expect(v.x_open(base, open_main_db() + open_readwrite())).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(rt_file_exists(base)).to_equal(false)
```

</details>

#### xOpen with CREATE+EXCLUSIVE refuses an existing file

- Verify: xOpen with CREATE+EXCLUSIVE refuses an existing file
   - Expected: h equals `0`
   - Expected: v.x_open(base, open_main_db() + open_create() + open_exclusive()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xOpen with CREATE+EXCLUSIVE refuses an existing file")
val base = tpath("excl")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
expect(h).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(v.x_open(base, open_main_db() + open_create() + open_exclusive())).to_equal(-1)  # oracle: -1 — named expected value from the requirement
v.x_close(h)
clean(base)
```

</details>

#### DELETEONCLOSE removes the file on xClose

- Verify: DELETEONCLOSE removes the file on xClose
   - Expected: rt_file_exists(base) is true
   - Expected: v.x_close(h) equals `sqlite_ok()`
   - Expected: rt_file_exists(base) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: DELETEONCLOSE removes the file on xClose")
val base = tpath("delonclose")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags() + open_deleteonclose())
expect(rt_file_exists(base)).to_equal(true)
expect(v.x_close(h)).to_equal(sqlite_ok())
expect(rt_file_exists(base)).to_equal(false)
```

</details>

#### xDelete of a missing file is OK, of an existing file removes it

- Verify: xDelete of a missing file is OK, of an existing file removes it
   - Expected: v.x_delete(base, false) equals `sqlite_ok()`
   - Expected: rt_file_exists(base) is true
   - Expected: v.x_delete(base, true) equals `sqlite_ok()`
   - Expected: rt_file_exists(base) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xDelete of a missing file is OK, of an existing file removes it")
val base = tpath("del")
clean(base)
var v = new_vfs()
expect(v.x_delete(base, false)).to_equal(sqlite_ok())
val h = v.x_open(base, db_flags())
v.x_close(h)
expect(rt_file_exists(base)).to_equal(true)
expect(v.x_delete(base, true)).to_equal(sqlite_ok())
expect(rt_file_exists(base)).to_equal(false)
```

</details>

#### xFullPathname normalizes . .. duplicate slashes and trailing slash

- Verify: xFullPathname normalizes . .. duplicate slashes and trailing slash
   - Expected: normalize_full_path("/w", "a/b") equals `/w/a/b`
   - Expected: normalize_full_path("/w", "a//b") equals `/w/a/b`
   - Expected: normalize_full_path("/w", "./a/./b") equals `/w/a/b`
   - Expected: normalize_full_path("/w", "a/../b") equals `/w/b`
   - Expected: normalize_full_path("/w", "a/b/") equals `/w/a/b`
   - Expected: normalize_full_path("/w", "/abs/p") equals `/abs/p`
   - Expected: normalize_full_path("/w", "/abs//p/../q/") equals `/abs/q`
   - Expected: normalize_full_path("/w", "..") equals `/`
   - Expected: normalize_full_path("/w", ".") equals `/w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xFullPathname normalizes . .. duplicate slashes and trailing slash")
expect(normalize_full_path("/w", "a/b")).to_equal("/w/a/b")
expect(normalize_full_path("/w", "a//b")).to_equal("/w/a/b")
expect(normalize_full_path("/w", "./a/./b")).to_equal("/w/a/b")
expect(normalize_full_path("/w", "a/../b")).to_equal("/w/b")
expect(normalize_full_path("/w", "a/b/")).to_equal("/w/a/b")
expect(normalize_full_path("/w", "/abs/p")).to_equal("/abs/p")
expect(normalize_full_path("/w", "/abs//p/../q/")).to_equal("/abs/q")
expect(normalize_full_path("/w", "..")).to_equal("/")
expect(normalize_full_path("/w", ".")).to_equal("/w")
```

</details>

#### xFullPathname through the VFS returns the normalized absolute path

- Verify: xFullPathname through the VFS returns the normalized absolute path
   - Expected: fp.code equals `sqlite_ok()`
   - Expected: fp.path equals `/base/x.db`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xFullPathname through the VFS returns the normalized absolute path")
var v = SqliteVfs.create("simpleos", "/base")
val fp = v.x_full_pathname("sub/../x.db")
expect(fp.code).to_equal(sqlite_ok())
expect(fp.path).to_equal("/base/x.db")
```

</details>

#### journal path derivation and detection are consistent

- Verify: journal path derivation and detection are consistent
   - Expected: journal_path_for("/d/a.db") equals `/d/a.db-journal`
   - Expected: path_is_journal("/d/a.db-journal") is true
   - Expected: path_is_journal("/d/a.db") is false
   - Expected: parent_dir_of("/d/a.db") equals `/d`
   - Expected: parent_dir_of("/a.db") equals `/`
   - Expected: parent_dir_of("a.db") equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: journal path derivation and detection are consistent")
expect(journal_path_for("/d/a.db")).to_equal("/d/a.db-journal")
expect(path_is_journal("/d/a.db-journal")).to_equal(true)
expect(path_is_journal("/d/a.db")).to_equal(false)
expect(parent_dir_of("/d/a.db")).to_equal("/d")
expect(parent_dir_of("/a.db")).to_equal("/")
expect(parent_dir_of("a.db")).to_equal(".")
```

</details>

#### xRandomness returns the requested count and xSleep sleeps at least as long as asked

- Verify: xRandomness returns the requested count and xSleep sleeps at least as long as asked
   - Expected: v.x_randomness(16).len() equals `16`
   - Expected: v.x_randomness(0).len() equals `0`
   - Expected: v.x_sleep(0) equals `0`
   - Expected: v.x_sleep(1000) equals `1000`
   - Expected: v.x_sleep(1500) >= 1500 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xRandomness returns the requested count and xSleep sleeps at least as long as asked")
var v = new_vfs()
expect(v.x_randomness(16).len()).to_equal(16)  # oracle: 16 — named expected value from the requirement
expect(v.x_randomness(0).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(v.x_sleep(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(v.x_sleep(1000)).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
expect(v.x_sleep(1500) >= 1500).to_equal(true)
```

</details>

#### xCurrentTime returns a plausible Julian Day and the int64 form agrees

- Verify: xCurrentTime returns a plausible Julian Day and the int64 form agrees
   - Expected: jd > 2460000.0 is true
   - Expected: jd < 2500000.0 is true
   - Expected: v.x_current_time_int64() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xCurrentTime returns a plausible Julian Day and the int64 form agrees")
var v = new_vfs()
val jd = v.x_current_time()
# 2440587.5 is the Unix epoch; anything sane is well past 2460000 (2023).
expect(jd > 2460000.0).to_equal(true)
expect(jd < 2500000.0).to_equal(true)
expect(v.x_current_time_int64() > 0).to_equal(true)
```

</details>

### SQLite VFS impl — unsupported surface fails CLOSED

#### every shared-memory method returns its real SQLITE_IOERR_SHM* code

- Verify: every shared-memory method returns its real SQLITE_IOERR_SHM* code
   - Expected: v.x_shm_map(h, 0, 32768, true) equals `sqlite_ioerr_shmmap()`
   - Expected: v.x_shm_lock(h, 0, 1, 0) equals `sqlite_ioerr_shmlock()`
   - Expected: v.x_shm_barrier(h) equals `sqlite_ioerr_shmmap()`
   - Expected: v.x_shm_unmap(h, true) equals `sqlite_ioerr_shmmap()`
   - Expected: v.x_shm_open(h) equals `sqlite_ioerr_shmopen()`
   - Expected: v.x_shm_map(h, 0, 32768, true) == sqlite_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: every shared-memory method returns its real SQLITE_IOERR_SHM* code")
val base = tpath("shm")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
expect(v.x_shm_map(h, 0, 32768, true)).to_equal(sqlite_ioerr_shmmap())
expect(v.x_shm_lock(h, 0, 1, 0)).to_equal(sqlite_ioerr_shmlock())
expect(v.x_shm_barrier(h)).to_equal(sqlite_ioerr_shmmap())
expect(v.x_shm_unmap(h, true)).to_equal(sqlite_ioerr_shmmap())
expect(v.x_shm_open(h)).to_equal(sqlite_ioerr_shmopen())
# never SQLITE_OK — that is the bug this test exists to prevent
expect(v.x_shm_map(h, 0, 32768, true) == sqlite_ok()).to_equal(false)
v.x_close(h)
clean(base)
```

</details>

#### WAL stays gated and says exactly what it is waiting on

- Verify: WAL stays gated and says exactly what it is waiting on
   - Expected: impl_wal_supported() is false
   - Expected: impl_status_of("xShmMap").status equals `unsupported`
   - Expected: impl_rollback_journal_supported() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: WAL stays gated and says exactly what it is waiting on")
expect(impl_wal_supported()).to_equal(false)
expect(impl_status_of("xShmMap").status).to_equal("unsupported")
expect(impl_wal_blocked_prerequisite()).to_contain("shared mmap")
# rollback-journal mode, by contrast, is real
expect(impl_rollback_journal_supported()).to_equal(true)
```

</details>

#### xDeviceCharacteristics claims NO unproven IOCAP bit

- Verify: xDeviceCharacteristics claims NO unproven IOCAP bit
   - Expected: v.x_device_characteristics(h) equals `0`
   - Expected: v.x_sector_size(h) equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xDeviceCharacteristics claims NO unproven IOCAP bit")
val base = tpath("iocap")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
expect(v.x_device_characteristics(h)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(v.x_sector_size(h)).to_equal(512)  # oracle: 512 — named expected value from the requirement
v.x_close(h)
clean(base)
```

</details>

#### xFileControl handles the two opcodes it claims and returns NOTFOUND for the rest

- Verify: xFileControl handles the two opcodes it claims and returns NOTFOUND for the rest
   - Expected: v.x_file_control(h, fcntl_size_hint()) equals `sqlite_ok()`
   - Expected: v.x_file_control(h, fcntl_has_moved()) equals `sqlite_ok()`
   - Expected: v.x_file_control(h, 9999) equals `sqlite_notfound()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: xFileControl handles the two opcodes it claims and returns NOTFOUND for the rest")
val base = tpath("fcntl")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
expect(v.x_file_control(h, fcntl_size_hint())).to_equal(sqlite_ok())
expect(v.x_file_control(h, fcntl_has_moved())).to_equal(sqlite_ok())
expect(v.x_file_control(h, 9999)).to_equal(sqlite_notfound())
v.x_close(h)
clean(base)
```

</details>

#### operations on a closed or bogus handle fail rather than corrupting

- Verify: operations on a closed or bogus handle fail rather than corrupting


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: operations on a closed or bogus handle fail rather than corrupting")
val base = tpath("badh")
clean(base)
var v = new_vfs()
val h = v.x_open(base, db_flags())
v.x_close(h)
expect(v.x_write(h, 0, bytes_from_text("x"))).to_not_equal(sqlite_ok())
expect(v.x_read(h, 0, 4).code).to_not_equal(sqlite_ok())
expect(v.x_sync(h, sync_normal())).to_not_equal(sqlite_ok())
expect(v.x_truncate(h, 0)).to_not_equal(sqlite_ok())
expect(v.x_write(4242, 0, bytes_from_text("x"))).to_not_equal(sqlite_ok())
expect(v.x_file_size(4242).code).to_not_equal(sqlite_ok())
clean(base)
```

</details>

#### the implementation status table is honest about what is real

- Verify: the implementation status table is honest about what is real
   - Expected: impl_status_of("xTruncate").status equals `supported`
   - Expected: impl_status_of("xSync").status equals `supported`
   - Expected: impl_status_of("xLock").status equals `partial`
   - Expected: impl_status_of("xUnlock").status equals `partial`
   - Expected: impl_status_of("xCheckReservedLock").status equals `partial`
   - Expected: impl_status_of("xDeviceCharacteristics").status equals `partial`
   - Expected: impl_status_of("xShmMap").status equals `unsupported`
   - Expected: impl_status_of("xShmLock").status equals `unsupported`
   - Expected: impl_status_of("xShmBarrier").status equals `unsupported`
   - Expected: impl_status_of("xShmUnmap").status equals `unsupported`
   - Expected: impl_count_with_status("unsupported") equals `4`
   - Expected: impl_count_with_status("partial") equals `5`
   - Expected: impl_count_with_status("supported") equals `14`
   - Expected: impl_status_of("xNoSuchMethod").status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: the implementation status table is honest about what is real")
expect(impl_status_of("xTruncate").status).to_equal("supported")
expect(impl_status_of("xSync").status).to_equal("supported")
expect(impl_status_of("xLock").status).to_equal("partial")
expect(impl_status_of("xUnlock").status).to_equal("partial")
expect(impl_status_of("xCheckReservedLock").status).to_equal("partial")
expect(impl_status_of("xDeviceCharacteristics").status).to_equal("partial")
expect(impl_status_of("xShmMap").status).to_equal("unsupported")
expect(impl_status_of("xShmLock").status).to_equal("unsupported")
expect(impl_status_of("xShmBarrier").status).to_equal("unsupported")
expect(impl_status_of("xShmUnmap").status).to_equal("unsupported")
expect(impl_count_with_status("unsupported")).to_equal(4)
expect(impl_count_with_status("partial")).to_equal(5)
expect(impl_count_with_status("supported")).to_equal(14)
expect(impl_status_of("xNoSuchMethod").status).to_equal("unsupported")
```

</details>

#### the amalgamation build is still reported blocked

- Verify: the amalgamation build is still reported blocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT-001
step("Verify: the amalgamation build is still reported blocked")
expect(amalgamation_build_status()).to_contain("blocked")
expect(amalgamation_build_status()).to_contain("C toolchain")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
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

- Canonical SPipe generation for source `3da151868e66eff493b0e218bce6dfd39cda3dd38259d22e0aca506ac9763c86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3da151868e66eff493b0e218bce6dfd39cda3dd38259d22e0aca506ac9763c86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3da151868e66eff493b0e218bce6dfd39cda3dd38259d22e0aca506ac9763c86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl
mirror: doc/06_spec/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read-after-write returns exactly the bytes written' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an offset write lands at the offset and leaves the prefix intact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a write past EOF zero-fills the hole, like pwrite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

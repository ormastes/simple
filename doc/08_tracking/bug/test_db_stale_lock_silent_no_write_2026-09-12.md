# A stale `{path}.lock` makes `write_db_file_locked` report success while writing nothing

- Status: OPEN (2026-09-12)
- Area: lib / test_runner / test database I/O
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 prefix `3d120a6f` (`Simple Language v1.0.0-rc.1`, Rust bootstrap seed)
- Found while implementing todo rows 233-243 (test database concurrency specs)

## Symptom

`std.test_runner.test_db_io.write_db_file_locked(path, content)` returns `Ok(())`
and the calling code sees no error, but **no file is created at `path`**. The
only artifact left on disk is the lock sidecar `{path}.lock`, containing
`<pid>:<token>` (e.g. `124072B:spark-f0ce`).

This is a fail-open: the one signal a caller has (the `Result`) says the write
landed.

## Repro (observed, not reconstructed)

1. Run a spec that calls `write_db_file_locked` against a fresh scratch path and
   aborts before the lock is released. In the observed case the abort was the
   Option-vs-Result `match` defect fixed in the same change
   (`src/lib/nogc_sync_mut/test_runner/test_db_io.spl`) — the process died
   between `TestDbFileLock.acquire` and `lock.release()`.
2. `{path}.lock` survives the dead process. Confirmed on disk:

   ```
   -rw-rw-r-- 1 yoon yoon 18 Sep 12 15:32 build/test/.../write.sdn.lock
   -rw-rw-r-- 1 yoon yoon 18 Sep 12 15:32 build/test/.../read.sdn.lock
   ```

   with no `write.sdn` / `read.sdn` beside them.
3. Re-run the same spec. `write_db_file_locked` returns `Ok`, the test's
   subsequent `file_read(path)` yields `""`, and the target file still does not
   exist. Paths whose lock sidecar was *not* stale (`backup.sdn`,
   `empty_guard.sdn`) wrote correctly in the same process.
4. `rm -rf` the scratch directory and re-run: all five scenarios pass
   (`5 examples, 0 failures`).

So the failure is entirely a function of an inherited `.lock` sidecar, and it is
order-dependent across runs rather than within one.

## Why this matters beyond the specs

`write_db_file_locked` / `update_db_file` are the path-parameterized writers for
the test database. A crashed or killed test run leaves a stale lock next to
`doc/08_tracking/test/test_db.sdn`; every later run then reports a successful
save while recording nothing. That is the same class of silent-darkness failure
already recorded for the cold-start path in
`test/01_unit/lib/test_runner/test_db_cold_start_spec.spl`.

## Expected

Either:

- `TestDbFileLock.acquire` detects a stale lock (holder pid no longer alive) and
  reclaims it — the stale-lock detection the concurrency spec's
  "detects and cleans stale lock files" scenario describes but does not yet
  enforce; or
- `file_atomic_write` failing under a held lock returns `false` so
  `write_db_file_locked` surfaces `Err`, never `Ok`.

Reporting `Ok` for a write that produced no file is wrong under either choice.

## Not fixed here

Out of scope for the todo rows being implemented (stale-lock reclamation is a
locking-policy decision in `src/lib/nogc_sync_mut/test_runner/test_db_lock.spl`
and the `file_lock` SFFI beneath it, touching every test-database writer). The
specs added alongside this record clear `{path}.lock` in their own setup so they
are deterministic, and this record exists so that workaround is not mistaken for
the fix.

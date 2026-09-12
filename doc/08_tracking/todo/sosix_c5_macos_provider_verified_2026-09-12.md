# TODO#23 (sosix C5) — macOS half verified, Windows half still open

**Item:** `doc/TODO.md` #23 / `todo_db.sdn` row 23 —
"(sosix C5) add the macOS and Windows providers on a host that has them; this
[path is the portable fallback, not their replacement]"
(`src/lib/nogc_async_mut/sosix/file_driver.spl:16`).

## Finding (macOS arm64, 2026-09-12, seed `build/cargo-r2/release/simple`)

`SosixHostedFileDriver` (the "reference hosted provider" in that file) is
already platform-generic: it services ring submissions through
`std.nogc_async_mut.io.{file_read_text_at, file_write_text_at}`, which are
POSIX `open`+`pread`/`pwrite`+`close` wrappers, not Linux-specific. Nothing in
the file gates on `target_os` or depends on `io_uring` (that dependency is
scoped to the separate C4 TODO, one line above, for a *Linux* io_uring
provider — a performance upgrade, not a portability requirement).

Ran the dedicated spec directly on this host (the `simple test` subcommand is
independently broken here — see
`macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot`,
Lane 3 of `doc/03_plan/infra/macos_open_bugs_fix_lanes_2026-09-12.md` — so
`simple run` was used, which loads and executes the same spec body):

```
$ simple run test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl
SOSIX reference file driver on the host filesystem
  ✓ writes bytes through the ring and reads the same bytes back through the ring
  ✓ reports a short read past the end of the file as partial progress
  ✓ surfaces a missing file as a typed native error after exactly one wait
  ✓ refuses a write whose buffer window starts past the buffer end without touching the file
4 examples, 0 failures
```

All 4 examples pass unmodified on macOS — real positioned file I/O against
this host's filesystem, exercised through the same ring/capability-table path
Linux uses. **The macOS half of TODO#23 is therefore already satisfied by the
existing portable reference provider; no macOS-specific code was needed or
added.**

## What remains open

- **Windows provider** — not attempted here (no Windows host available in
  this session). `file_read_text_at`/`file_write_text_at`'s Windows path (if
  any) has not been audited for `pread`/`pwrite`-equivalent positioned I/O
  semantics (`ReadFile`/`WriteFile` with `OVERLAPPED`, or `_lseeki64` +
  `_read`/`_write`). Resume on a Windows host: run this same spec
  (`test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl`) via
  `bin/simple run` (not `simple test`, per the runner defect above unless
  already fixed); if it fails, the gap is in the underlying
  `file_read_text_at`/`file_write_text_at` Windows implementation, not in
  `file_driver.spl` itself.
- **C4 (Linux io_uring)** — unrelated, unaffected by this finding, still open.

## Disposition

`todo_db.sdn` row 23's description is updated in this change to record the
macOS evidence above and narrow the remaining scope to Windows; the row stays
`open` (Windows is unverified) rather than `closed`.

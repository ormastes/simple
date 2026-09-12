# TODO#23 (sosix C5) — fallback verified no-portability-gap on macOS; native providers still open

**Item:** `doc/TODO.md` #23 / `todo_db.sdn` row 23 —
"(sosix C5) add the macOS and Windows providers on a host that has them; this
path is the portable fallback, not their replacement"
(`src/lib/nogc_async_mut/sosix/file_driver.spl:16`).

The TODO's own wording already says the reference provider is a fallback, not
a replacement for real per-OS providers — the intended C5 deliverable is a
native macOS provider (the kqueue/`dispatch_io`-class analog of C4's Linux
io_uring provider) and a native Windows provider. This entry does **not**
claim that work is done. It records one narrower, verified fact.

## Finding (macOS arm64, 2026-09-12, seed `build/cargo-r2/release/simple`)

`SosixHostedFileDriver` (the reference/fallback provider in that file)
services ring submissions through
`std.nogc_async_mut.io.{file_read_text_at, file_write_text_at}`, POSIX
`open`+`pread`/`pwrite`+`close` wrappers with no `target_os` gate and no
`io_uring` dependency (that dependency belongs to the separate C4 TODO one
line above, for a *Linux* io_uring provider).

Ran the dedicated spec directly on this host (`bin/simple test` is
independently broken here — see
`macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot`, Lane 3 of
`doc/03_plan/infra/macos_open_bugs_fix_lanes_2026-09-12.md` — so `bin/simple
run` was used instead, which loads and executes the same spec body but does
not exercise the `test` runner harness):

```
$ simple run test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl
SOSIX reference file driver on the host filesystem
  ✓ writes bytes through the ring and reads the same bytes back through the ring
  ✓ reports a short read past the end of the file as partial progress
  ✓ surfaces a missing file as a typed native error after exactly one wait
  ✓ refuses a write whose buffer window starts past the buffer end without touching the file
4 examples, 0 failures
```

All 4 examples pass unmodified on macOS. **Verified: the fallback provider
itself has no macOS portability gap** — it runs real positioned file I/O
against this host's filesystem today, before any native provider exists. This
is a narrower claim than "the macOS provider is implemented": no kqueue /
`dispatch_io`-based native provider was written, and none is implied by this
result.

## What remains open (unchanged in substance, just re-scoped)

- **Native macOS provider** — still not implemented. Prerequisite: the same
  class of blocker as C4 — the runtime would need to expose kqueue or
  `dispatch_io` externs (or an equivalent macOS async I/O primitive) before a
  distinct native provider (as opposed to the portable fallback) can be
  written and would offer anything over `file_read_text_at`/`file_write_text_at`.
- **Native Windows provider** — not attempted here (no Windows host in this
  session). Resume on a Windows host: run
  `test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl` via `bin/simple
  run` (not `simple test`, per the runner defect above, unless already fixed)
  to establish whether the *fallback* also has no Windows portability gap
  first; if it fails, the gap is in the underlying
  `file_read_text_at`/`file_write_text_at` Windows implementation, not in
  `file_driver.spl` itself. A native Windows provider is separate follow-on
  work regardless of that result.
- **C4 (Linux io_uring)** — unrelated, unaffected by this finding, still open.

## Disposition

`todo_db.sdn` row 23's `description` and `blocked` columns are updated in this
change to record the macOS fallback evidence above; the row stays `open` —
neither the macOS nor the Windows native-provider work is done.

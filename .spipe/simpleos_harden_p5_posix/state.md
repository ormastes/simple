# Lane P5 — POSIX Truth

## Goal

Publish an honest POSIX profile matrix (Profiles A–D) for SimpleOS, stop any
implicit claim of unsupported conformance (`_POSIX_VERSION` must never be
`202405L`), and find + fix-closed the worst silent-fake-success stub in
`src/os/posix/**` / `src/os/libc/**` — with a spec that proves it.

## Matrix summary (doc/02_requirements/os/posix_profiles.md)

- implemented: 20
- partial: 5
- stub (honest ENOSYS/error): 9
- absent: 6
- DISHONEST (open defect, filed not fixed): 1 (`flock()`)
- `_POSIX_VERSION`: confirmed not defined anywhere in `src/os/libc/` or
  `src/os/posix/` (grep, zero hits) — correct, must stay that way.

## Honest-failure fix (this increment)

`src/os/libc/simpleos_libc.c`, `mmap()` (SimpleOS-kernel syscall branch,
`running_on_linux_host() == false`; the Linux-host passthrough branch was
already honest). Previously: `(void)flags; (void)fd; (void)offset;` then
dispatched `simpleos_syscall(10, ...)` unconditionally — a writable
`MAP_SHARED` request or any file-backed (`fd >= 0`) request silently got back
an anonymous private mapping that looked like success. Fixed at
`src/os/libc/simpleos_libc.c:176-184` (post-fix line numbers): now fails
closed with `errno = EOPNOTSUPP; return MAP_FAILED;` for
`(flags & MAP_SHARED) != 0 && (prot & PROT_WRITE) != 0` and for `fd >= 0`.
Anonymous `MAP_PRIVATE` mappings (the common allocator case) are unaffected —
still the real `simpleos_syscall(10, ...)` path.

Also audited (already honest, no fix needed): `pthread_create/join/detach`
(`ENOSYS`), `tcgetattr`/`tcsetattr`/`tcflush`/`tcdrain`/`tcsendbreak`/`tcflow`
(`ENOSYS`, with documented reasoning), `eventfd`/`signalfd`/`timerfd`/
`inotify_*` (`ENOSYS`), PE `dlopen` (`Invalid`, not fake success).

Second dishonest stub found and filed but NOT fixed this bounded increment
(only one "worst lie" fix was in scope): `flock()` in
`src/os/libc/simpleos_filelock.c` unconditionally returns `0` for every
operation including `LOCK_EX`, with zero lock-state tracking. See "Follow-up"
section of the profile doc.

## Spec verdict

`test/01_unit/os/posix/posix_honest_failure_spec.spl`:
- Against the fixed source: `4 examples, 0 failures` (mmap group) +
  `2 examples, 0 failures` (pthread group) = 6/6 passing.
- Proved the spec can fail: temporarily reverted `simpleos_libc.c` to the
  pre-fix (git HEAD) text and reran — got `4 examples, 3 failures` in the
  mmap group (the `EOPNOTSUPP`/`fd >= 0`/no-longer-discards checks all
  correctly failed); pthread group still passed 2/2 as expected since that
  file was untouched. Restored the fixed source afterward and reran to
  confirm green again (6/6).
- Run via the documented recipe: `/tmp/p5lane/bin/p5job run
  test/01_unit/os/posix/posix_honest_failure_spec.spl` (p5job =
  `bin/release/x86_64-unknown-linux-gnu/simple`, self-hosted, not the seed).

The spec is a source-contract spec (reads
`src/os/libc/simpleos_libc.c`/`simpleos_pthread.c` text via
`app.io.mod.file_read_text` and asserts on it), not an executed-branch spec:
the guest-only `mmap()` branch only runs when `running_on_linux_host()` is
false, which cannot be forced from a host-Linux-compiled test binary run by
`simple run` (a host-compiled probe would take the already-honest Linux
passthrough branch instead and prove nothing about the fixed branch). This
is noted as a limitation in the spec's docstring.

## Blockers

- None blocking this increment's deliverables. Two items filed for a future
  P5 increment: (1) fix `flock()` to fail closed (`ENOSYS`) or implement real
  advisory locking; (2) AF_UNIX, shm, and AIO are fully absent (Profile C) —
  not attempted this increment, out of the "bounded first increment" scope.
- Did not run a full bootstrap/build of `src/os/libc` (C, compiled via the
  separate cross-toolchain Makefile, not part of `bin/simple build`); the fix
  was verified by direct source inspection + the source-contract spec above,
  consistent with "T0–T2 verification per lane; T3 bootstrap only if compiler
  source touched" — no compiler source was touched.

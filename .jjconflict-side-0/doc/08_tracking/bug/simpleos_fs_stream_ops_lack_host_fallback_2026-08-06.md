# SimpleOS libc: fopen/fread/fwrite bypass the Linux-host syscall fallback

Status: FIXED (2026-08-10)
Found: 2026-08-06, while fixing
`simpleos_libc_file_struct_odr_mismatch_2026-08-06.md`

## Fix (2026-08-10)

Implemented the "better" option from the original report: the FILE-stream layer
in `src/os/libc/simpleos_fs.c` no longer calls `simpleos_syscall` with hardcoded
numbers for open/read/write/close/seek. It now calls the libc's own
`open`/`read`/`write`/`close`/`lseek` (all defined with `running_on_linux_host()`
dispatch in `simpleos_libc.c`, and `lseek` in `simpleos_fs.c` itself) instead:

- `fopen`, `freopen`: now call `open()` instead of `simpleos_syscall(30, ...)`.
- `fclose`: now calls `close()` instead of `simpleos_syscall(33, ...)`.
- `fread`, `fgets`, `fgetc`: now call `read()` instead of `simpleos_syscall(31, ...)`.
- `fwrite`: now calls `write()` instead of `simpleos_syscall(32, ...)`.
- `fseek`, `ftell`: now call the file's own `lseek()` (which already had a host
  fallback) instead of `simpleos_syscall(46, ...)`.

`opendir`/`readdir`/`closedir`/`rewinddir` were intentionally left untouched —
directory listing has no Linux-host equivalent worth emulating and was not part
of the reported gap.

### Verification (host x86_64 Linux, real execution, not simulated)

Compiled `src/os/libc/simpleos_fs.c` + `simpleos_libc.c` +
`src/os/libc/test/file_stream_roundtrip.c` as ordinary host objects (`gcc -O0
-g`, with minimal stand-in definitions for the freestanding-only symbols
`simpleos_syscall`/`simpleos_epoll_*`/`_fmt_float` that this test does not
exercise), linked, and ran the binary directly on the dev host.

Before the fix: `fopen("...", "w")` returned `NULL` (the FILE-stream syscall
numbers 30-33/46 collide with unrelated Linux x86_64 syscalls — 30 is `shmat`,
etc. — so on host they either erred or silently misbehaved), and the test's
Part 2 hit its `SKIP` branch.

After the fix: full round trip passes for real —
`fopen(w)`/`fwrite`/`fclose`/`fopen(r)`/`fread`/`memcmp` round-trip,
`fgetc`-to-`EOF` sets `feof`, `clearerr` clears it, std-stream state stays
intact throughout. Output: `RESULT: PASS (0)`, exit code 0, no `SKIP` line.

Also fixed a latent, unrelated bug found while verifying: the test's hardcoded
path `/tmp_file_stream_roundtrip.dat` is at the filesystem *root* (`/`), not
inside `/tmp/`, so it failed with `EACCES` for any non-root user — a red
herring that would have kept masking this exact fix as a false SKIP. Path is
now `/tmp/tmp_file_stream_roundtrip.dat`; the test also now prints `errno` on
an unexpected `fopen` failure instead of the old "no Linux-host fallback"
message that is no longer accurate.

No spec/build harness currently compiles+runs `file_stream_roundtrip.c`
automatically (it is a standalone regression probe with build instructions in
its header comment) — this remains true; a `check-*.shs` wrapper to run it on
every host-libc change would be a good follow-up but is out of scope here.

## Summary

`simpleos_libc.c` routes its POSIX primitives through a host check:

```c
static int running_on_linux_host(void);
ssize_t write(int fd, const void *buf, size_t count) {
    if (running_on_linux_host()) { ... linux_syscall3(1, ...) ... }
    ... simpleos_syscall(32, ...) ...
}
```

so `write`/`read`/`stat`/`fstat` work when a SimpleOS-targeted binary is run
directly on a Linux host. The FILE-stream layer in `simpleos_fs.c` does **not**:
`fopen` (30), `fread` (31), `fwrite` (32), `fseek`/`ftell` (46) and `fclose`
(33) call `simpleos_syscall` unconditionally.

Those numbers mean something else entirely on Linux x86_64 — 30 is `shmat`,
31 `shmctl`, 32 `dup`, 33 `dup2`, 46 `sendmsg` — so on a host the calls do not
fail cleanly, they perform an unrelated operation and return a plausible-looking
value. `fwrite(..., stdout)` returns a nonzero count having written nothing.

## Impact

Not a correctness bug in-guest; the syscall numbers are right there. It is a
**testability** bug: any host-side smoke test of the libc silently loses the
whole stream layer, and a wrong-syscall return is indistinguishable from success
at the call site.

Observed directly: `src/os/libc/test/file_stream_roundtrip.c` links and runs on
the host, and its `fprintf`/`fputs`/`feof`/`ferror`/`fileno`/`clearerr` checks
pass, but `fopen` returns NULL and `fwrite(stdout)` returns a bogus count. The
test now probes `fopen` once and skips the syscall-backed half rather than
reporting a spurious failure.

## Fix

Give `simpleos_fs.c` the same `running_on_linux_host()` dispatch
`simpleos_libc.c` already uses — or, better, have the stream layer call the
libc's own `open`/`read`/`write`/`close`/`lseek` wrappers instead of
`simpleos_syscall` directly, so the fallback is honoured in exactly one place.
The second form also removes five hardcoded syscall numbers from the stream
layer.

## Not fixed here

Deliberately out of scope of the FILE-ODR fix: it changes the behaviour of the
very functions that change was proving, so it wants its own change and its own
evidence.

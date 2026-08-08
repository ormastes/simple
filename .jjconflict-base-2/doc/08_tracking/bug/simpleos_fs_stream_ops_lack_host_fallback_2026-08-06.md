# SimpleOS libc: fopen/fread/fwrite bypass the Linux-host syscall fallback

Status: OPEN
Found: 2026-08-06, while fixing
`simpleos_libc_file_struct_odr_mismatch_2026-08-06.md`

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

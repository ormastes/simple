# `rt_stdin_read_timeout_v1` restarts its deadline after `EINTR`

## Symptom

The Linux implementation polls stdin with the full caller timeout every time
`poll` returns `EINTR`. A signal near the end of the requested interval can
therefore extend a supposedly bounded read by another full interval. The
absolute deadline should govern the entire wait, including interrupted polls.

## Scope

This finding concerns only the timeout guarantee for `rt_stdin_read_timeout_v1`
in `src/runtime/runtime_core_io_exports.c`. The adjacent retry around `read`
after readiness is not claimed to race or exceed the deadline here; it will be
evaluated separately against the API contract and a demonstrated fixture.

## Reproduction

The deterministic native fixture installs a no-op signal handler, uses an
unread pipe as stdin, and sends eight `SIGUSR1` signals to the polling thread.
It measures total duration with `CLOCK_MONOTONIC`. Against the unmodified
release source, a 300 ms timeout returned after 503 ms. After the fix, the
same fixture first returned after 302 ms. The final revision adds explicit
clock-failure and deadline-overflow guards; its one authorized rerun passed at
301 ms and exercised both injected guards.

## Expected behavior

Repeated `EINTR` must not reset the caller's requested timeout. The function
returns the empty byte array when the original deadline expires.

## Current evidence

Source inspection at release `80fdf9ff49f3adb37d43e38bea2039ed05923270`
shows the retry loop calls `poll(&pfd, 1, (int)timeout_ms)` with the unchanged
duration. The C fixture compiles the actual `runtime_core_io_exports.c` leaf;
only array ABI calls are stubbed; `clock_gettime` and `poll` are linker-wrapped
only to inject the two fail-closed guard cases. The final source SHA is
`988cb3bbb957c3ed20ef29d38b877c4e5d6fc7bd278190af3b5748b62c385758`. Its
retained artifacts are in `build/rt-stdin-timeout-eintr`.

The Simple facade caller is `sys.terminal_console.read_timeout`; `open()`
checks stdin is a TTY, enters raw mode, and enforces one console handle owner.
The test substitutes an unread pipe to make EINTR timing deterministic. This
does not establish a competing-reader race after poll readiness, so the
post-read EINTR retry remains outside this finding.

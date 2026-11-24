# rt_file_lock (runtime_native.c) uses mixed close spellings

- **Status:** open
- **Severity:** low (consistency and maintainability; no behaviour difference found)
- **Found:** 2026-11-24, during the Win32/POSIX de-duplication review (plan P3, which is NO-GO)
- **Location:** `src/runtime/runtime_native.c`, `rt_file_lock` / `rt_file_unlock` (about lines 15007-15090 on release/1.0.0 at 9ad6ef27f18)

## Observation

The descriptor is opened with `rt_crt_open()`, but the close calls are spelled three different ways:

| branch | close calls used |
|---|---|
| `_WIN32` | `_close(fd)` at the `_get_osfhandle` failure, the timeout-0 failure, the hard-error, the deadline and the unlock paths |
| POSIX | `rt_crt_close(fd)` at timeout 0 and at the deadline; bare `close(fd)` at the hard-error (`errno`) path and in `rt_file_unlock` |

`runtime_crt_file.h` defines `rt_crt_close` as `_close` on Windows and as `close` elsewhere. So today every spelling resolves to the same call, and there is no functional bug.

## Why it matters

- If `rt_crt_close` ever gains bookkeeping (fd tracking, EINTR policy), the bare `_close`/`close` sites will silently bypass it.
- The asymmetry also blocked a mechanical de-duplication of the lock poll loop (plan P3): sharing the loop would have quietly "fixed" the spellings.

## Fix (when picked up)

- Use `rt_crt_close` at every close site in both functions. Make no other change.
- Pin the result with `src/runtime/test/runtime_file_lock_zero_timeout_v2_test.c` and a contended-timeout case.

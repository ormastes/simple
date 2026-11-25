# rt_file_lock (runtime_native.c) uses mixed close spellings

- **Status:** fixed
- **Severity:** low (consistency and maintainability; no behaviour difference found)
- **Found:** 2026-11-24, during the Win32/POSIX de-duplication review (plan P3, which is NO-GO)
- **Fixed:** 2026-11-25, replaced all 7 raw `_close(fd)` / `close(fd)` sites in `rt_file_lock` and `rt_file_unlock` with `rt_crt_close(fd)`
- **Location:** `src/runtime/runtime_native.c`, `rt_file_lock` / `rt_file_unlock` (lines 14640-14724)

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

## Fix (implemented)

- Replaced all 7 bare `_close(fd)` / `close(fd)` sites in `rt_file_lock` and `rt_file_unlock` (`src/runtime/runtime_native.c`) with `rt_crt_close(fd)` (4 `_WIN32` error/close sites and 1 POSIX hard-error site in `rt_file_lock`; both `_WIN32` and POSIX close sites in `rt_file_unlock`). Made no other change.
- Verified with:
  - `src/runtime/test/rt_file_lock_windows_selfcheck.c` (wired into `scripts/check/check-bootstrap-windows-c-admission.shs` and run against both `runtime_native.c` and `runtime_host_file_exports.c`).
  - `src/runtime/test/rt_file_lock_crt_close_selfcheck.c` (standalone C selfcheck covering `rt_crt_open`/`rt_crt_close`, `rt_file_lock` error/contention paths, `rt_file_unlock` negative-fd safety, and zero-leak cleanup against `runtime_native.c`, compiled and run on Windows `llvm-mingw`, Windows `clang-cl /MD`, and Linux `clang-18`).
- Note: `src/runtime/test/runtime_file_lock_zero_timeout_v2_test.c` targets the legacy `runtime.c` / `platform/unix_common.h` provider (`NOT_RUN`, excludes `runtime_native.c`) and was left unmodified.

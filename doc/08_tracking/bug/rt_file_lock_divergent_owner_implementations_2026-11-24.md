# rt_file_lock / rt_file_unlock have two divergent owner implementations

- **Status:** open
- **Severity:** medium (same exported symbol, different contract depending on which owner is linked)
- **Found:** 2026-11-24, during the Win32/POSIX de-duplication review
- **Locations:**
  - `src/runtime/runtime_native.c` `rt_file_lock` (about line 15007 on release/1.0.0 at 9ad6ef27f18)
  - `src/runtime/runtime_host_file_exports.c:97` `rt_file_lock`, `:155` `rt_file_unlock`, selected by `SIMPLE_RUNTIME_HOST_FILE_EXPORTS_OWNER_V2`

## Divergence

| aspect | runtime_native.c | runtime_host_file_exports.c |
|---|---|---|
| Windows handle returned | CRT fd (`rt_crt_open` + `_get_osfhandle`) | raw `HANDLE` from `CreateFileA` |
| Windows path API | `rt_crt_open` = `_sopen_s` (narrow, ANSI code page) | `CreateFileA` (ANSI code page). Both mis-handle non-ASCII UTF-8 paths on a non-65001 ACP |
| path validation | `rt_text_arg_to_path` into `RT_TEXT_PATH_MAX` stack buffer | heap copy; rejects len 0, embedded NUL and len >= 4096 |
| `rt_file_unlock(0)` on POSIX | accepted (only fd < 0 rejected): unlocks and closes fd 0 | **returns true and closes stdin** (pinned by the test) |
| `rt_file_unlock(0)` on Windows | accepted: `UnlockFileEx` on CRT fd 0, then `_close(0)` | rejects 0 / -1 and returns false |
| POSIX open flags | `O_RDWR\|O_CREAT\|O_CLOEXEC` | `O_RDWR\|O_CREAT` (**no `O_CLOEXEC`**) |
| POSIX timeout loop | `CLOCK_MONOTONIC` deadline, EINTR retried | counted 50 ms sleeps, EINTR treated as a hard failure |

A handle from one owner is not valid input to the other owner's `rt_file_unlock`.

## Evidence

`src/runtime/test/rt_file_unlock_handle_characterization_selfcheck.c` pins the current behaviour of the host_file_exports owner. The golden output is in `rt_file_unlock_handle_characterization.{windows,posix}.golden.txt` (Windows: llvm-mingw clang; Linux: WSL ubuntu-p2 clang-18).

## Fix direction (owner decision)

1. Pick one contract: fd or HANDLE, and the UTF-8 path policy.
2. Make the other owner delegate to it.
3. Keep `O_CLOEXEC` and EINTR retry.
4. Reject handle 0 on POSIX.

Do this only after the characterization goldens are updated deliberately.

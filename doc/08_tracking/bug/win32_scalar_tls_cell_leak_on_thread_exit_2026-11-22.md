# Win32 scalar TLS: 8-byte cell leaks per thread on 32-bit targets

- **Status:** fixed
- **Severity:** P3 (bounded leak: 8 bytes × threads × live keys)
- **Area:** runtime / `src/runtime/runtime_thread.c`
- **Found:** 2026-11-22, Opus review of PR #10884 (merged bce61cae8d2)
- **Fixed:** 2026-11-24 (`work/mp1-win32-scalar-tls-fls`)

## Symptom
On 32-bit hosted targets (`SCALAR_TLS_INLINE == 0`, e.g. i686-w64-mingw32)
`rt_thread_local_set_i64` stores the value in a per-thread `malloc`'d
`int64_t` cell. On Win32 the key comes from `TlsAlloc`, which has no
destructor, so a thread that exits without calling `rt_thread_local_free`
leaks its cell. `rt_thread_local_free` frees only the calling thread's cell;
other threads' cells leak on Win32 and pthread alike (`pthread_key_delete`
runs no destructors).

## Resolution
- Switched Win32 scalar TLS in `src/runtime/runtime_thread.c` from `TlsAlloc` /
  `TlsGetValue` / `TlsSetValue` / `TlsFree` (`TLS_OUT_OF_INDEXES`) to Fiber
  Local Storage (`FlsAlloc` / `FlsGetValue` / `FlsSetValue` / `FlsFree` /
  `FLS_OUT_OF_INDEXES`), ensuring `_WIN32_WINNT >= 0x0600` before `<windows.h>`.
- Added `static VOID WINAPI scalar_tls_fls_free(PVOID cell)` (`__stdcall`) so
  32-bit x86 calling convention matches `PFLS_CALLBACK_FUNCTION` instead of
  passing `__cdecl` `free` directly.
- In `rt_thread_local_free` on Win32, delegated cell cleanup solely to
  `FlsFree(entry->key)` (which runs `scalar_tls_fls_free` once for every live
  thread/fiber with a non-NULL slot) so neither the calling thread nor live
  worker threads leak or double-free.
- Added `#ifdef SCALAR_TLS_FORCE_BOXED` (`SCALAR_TLS_INLINE 0`) and
  `#ifdef SIMPLE_SCALAR_TLS_SELFCHECK` (`SCALAR_TLS_CELL_ALLOC` /
  `SCALAR_TLS_CELL_FREE` hooks with atomic alloc/free/live counters) in
  `src/runtime/runtime_thread.c`.
- Extended `src/runtime/test/rt_thread_local_i64_selfcheck.c` with Win32
  `CreateThread` worker-exit leak checks, main+worker `rt_thread_local_free`
  checks, live-worker `FlsFree` + subsequent worker-exit double-free checks,
  read-only key checks, and slot-reuse churn checks.

## Verification
Verified with `C:/Users/user/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe`
and `i686-w64-mingw32-clang.exe` (temporary executables written to `$env:TEMP` and removed):

- Default 64-bit:
  `clang.exe -Wall -Wextra -I src/runtime src/runtime/runtime_thread.c src/runtime/test/rt_thread_local_i64_selfcheck.c -o $env:TEMP/sc_x64_default.exe && $env:TEMP/sc_x64_default.exe`
  -> `PASS rt_thread_local_i64` (exit 0)
- Boxed 64-bit leak + double-free check:
  `clang.exe -Wall -Wextra -DSCALAR_TLS_FORCE_BOXED=1 -DSIMPLE_SCALAR_TLS_SELFCHECK=1 -I src/runtime src/runtime/runtime_thread.c src/runtime/test/rt_thread_local_i64_selfcheck.c -o $env:TEMP/sc_x64_boxed.exe && $env:TEMP/sc_x64_boxed.exe`
  -> `PASS rt_thread_local_i64` (exit 0)
- Inline standalone 64-bit selfcheck:
  `clang.exe -Wall -Wextra -DSIMPLE_SCALAR_TLS_SELFCHECK=1 -DSIMPLE_CORE_C_STANDALONE=1 -I src/runtime src/runtime/runtime_thread.c src/runtime/test/rt_thread_local_i64_selfcheck.c -o $env:TEMP/sc_x64_inline_sc.exe && $env:TEMP/sc_x64_inline_sc.exe`
  -> `PASS rt_thread_local_i64` (exit 0)
- Native 32-bit (`i686-w64-mingw32`) with `_WIN32_WINNT=0x0501` floor check:
  `i686-w64-mingw32-clang.exe -Wall -Wextra -D_WIN32_WINNT=0x0501 -I src/runtime src/runtime/runtime_thread.c src/runtime/test/rt_thread_local_i64_selfcheck.c -o $env:TEMP/sc_i686_default.exe && $env:TEMP/sc_i686_default.exe`
  -> `PASS rt_thread_local_i64` (exit 0)
- Native 32-bit (`i686-w64-mingw32`) boxed leak + double-free check:
  `i686-w64-mingw32-clang.exe -Wall -Wextra -DSIMPLE_SCALAR_TLS_SELFCHECK=1 -I src/runtime src/runtime/runtime_thread.c src/runtime/test/rt_thread_local_i64_selfcheck.c -o $env:TEMP/sc_i686_sc.exe && $env:TEMP/sc_i686_sc.exe`
  -> `PASS rt_thread_local_i64` (exit 0)
- Syntax-only check:
  `clang.exe -fsyntax-only -Wall -Wextra -I src/runtime src/runtime/runtime_thread.c src/runtime/test/rt_thread_local_i64_selfcheck.c`
  -> exit 0

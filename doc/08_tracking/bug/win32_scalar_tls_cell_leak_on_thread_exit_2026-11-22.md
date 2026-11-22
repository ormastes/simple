# Win32 scalar TLS: 8-byte cell leaks per thread on 32-bit targets

- **Status:** open
- **Severity:** P3 (bounded leak: 8 bytes × threads × live keys)
- **Area:** runtime / `src/runtime/runtime_thread.c`
- **Found:** 2026-11-22, Opus review of PR #10884 (merged bce61cae8d2)

## Symptom
On 32-bit hosted targets (`SCALAR_TLS_INLINE == 0`, e.g. i686-w64-mingw32)
`rt_thread_local_set_i64` stores the value in a per-thread `malloc`'d
`int64_t` cell. On Win32 the key comes from `TlsAlloc`, which has no
destructor, so a thread that exits without calling `rt_thread_local_free`
leaks its cell. `rt_thread_local_free` frees only the calling thread's cell;
other threads' cells leak on Win32 and pthread alike (`pthread_key_delete`
runs no destructors).

## Fix direction
Use `FlsAlloc(free)` (fiber-local storage with a destructor callback) for the
32-bit Win32 path in place of `TlsAlloc`, mirroring the pthread
`free` destructor. Add a selfcheck that spawns threads which set a key and
exit, and asserts the cells are released (e.g. via a counting allocator hook).

## Repro
`src/runtime/test/rt_thread_local_i64_selfcheck.c` covers round-trip only; it
does not detect the leak. No check script runs that selfcheck yet (review note).

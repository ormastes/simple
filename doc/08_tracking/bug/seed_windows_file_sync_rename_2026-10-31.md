# Seed: rt_file_sync and rt_file_rename misbehave on Windows (2026-10-31)

Seed (Rust) interpreter externs; src/compiler_rust not edited. Product-side guard in
src/lib/nogc_sync_mut/database/atomic.spl (host_is_windows_host only; POSIX unchanged).

1. `rt_file_sync(path)` returns false for a freshly written file.
   `rt_file_fsync` (interpreter_extern/file_io.rs:797) opens read-only, then `sync_all()`;
   FlushFileBuffers needs write access on Windows.
   Repro: `file_write("x.txt","a"); print rt_file_sync("x.txt")` -> false.
2. `rt_file_rename(src, dst)` returns false when dst exists (file_io.rs:1273, fs::rename).
   Repro: write r1.txt and r2.txt; `file_rename("r2.txt","r1.txt")` -> false; after
   `file_delete("r1.txt")` the rename succeeds.

Effect before the guard: atomic_write always false, so `scv init` failed with
"cannot initialize status index".

Related, deliberately not loosened: `directory_fsync` (io/file_ops.spl:395) fails closed where
directories cannot be fsynced, so scv_journal_lock returns -1 ("journal lock unavailable") on
Windows for every mutating SCV spec. Owner decision needed.

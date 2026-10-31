# Seed: rt_file_sync and rt_file_rename misbehave on Windows (2026-10-31)

Seed (Rust) interpreter externs. A product-side guard in atomic.spl was rejected in review: it deleted
the destination before retrying rename, losing data on any rename failure. The fix belongs in the seed.

1. `rt_file_sync(path)` returns false for a freshly written file.
   `rt_file_fsync` (interpreter_extern/file_io.rs:797) opens read-only, then `sync_all()`;
   FlushFileBuffers needs write access on Windows.
   Repro: `file_write("x.txt","a"); print rt_file_sync("x.txt")` -> false.
2. `rt_file_rename(src, dst)` returns false when dst exists (file_io.rs:1273, fs::rename).
   Repro: write r1.txt and r2.txt; `file_rename("r2.txt","r1.txt")` -> false; after
   `file_delete("r1.txt")` the rename succeeds.

Effect: atomic_write is always false on the Windows seed, so `scv init` fails with
"cannot initialize status index".

Related, deliberately not loosened: `directory_fsync` (io/file_ops.spl:395) fails closed where
directories cannot be fsynced, so scv_journal_lock returns -1 ("journal lock unavailable") on
Windows for every mutating SCV spec. Owner decision needed.

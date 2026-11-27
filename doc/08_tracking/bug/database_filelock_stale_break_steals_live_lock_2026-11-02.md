# database FileLock stale-lock break and release can steal or destroy a live lock

Severity: P0. Location: src/lib/nogc_sync_mut/database/atomic.spl:114-126,129-160,163-170

## Interleaving
1. Lock L is stale (dead pid). A and B both run is_stale_lock() and get true.
2. A file_delete(L); A rt_file_create_excl(L) succeeds, A holds the lock.
3. B, already past its staleness check, file_delete(L) removes A's live lock; B create_excl succeeds. A and B both hold the lock and both mutate the database file.

Variant: is_stale_lock treats empty or one-line content as stale. If a contender reads the file between creation and content visibility, it deletes the brand new lock.

release() deletes the path without verifying it still holds our pid, so after a stale break A's release deletes B's lock and admits a third holder. Acquire polls with sleep_ms(10).

## Fix
Break stale locks by renaming L to a unique tombstone; only the rename winner proceeds. Never treat partially written content as stale. Release only when the content pid matches. Prefer the kernel lock used by db_atomic.spl file_lock.

## Stress spec
N processes loop acquire, non-atomic increment of a counter file, release; plant a stale lock first; assert counter equals total increments.

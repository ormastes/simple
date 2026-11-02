# daemon_sdk singleton lock is check-then-write, two daemons both acquire

Severity: P0. Location: src/lib/nogc_sync_mut/daemon_sdk/lock.spl:20-36,41-50

## Interleaving
1. A and B call try_acquire_daemon_lock(path) concurrently; no lock exists.
2. A: file_exists false. B: file_exists false.
3. A file_write(lock, A-pid). B file_write(lock, B-pid). Both return a pid; both daemons believe they own the singleton.

Variant (live lock stolen): A has created the file but not yet written content. B reads empty content, read_daemon_pid returns -1, B treats the holder as dead, deletes A's fresh lock and writes its own.

release_daemon_lock is also check-then-delete: it reads the pid, compares, then deletes; in between the lock may be replaced and the new owner's lock is deleted.

## Fix
Create with rt_file_create_excl (O_EXCL). Break a stale lock by renaming it to a unique tombstone and re-creating with O_EXCL. Treat empty content as "being written" (retry), not dead. Release only via the same rename step after verifying the pid.

## Stress spec
16 processes behind a start barrier call try_acquire_daemon_lock on one path; assert exactly one returns pid > 0 per round; 200 rounds.

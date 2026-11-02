# test runner ensure_daemon deletes a live daemon lock; light_daemon claim uses a shared tmp name

Severity: P0. Location: src/app/test_runner_new/test_runner_client.spl:331-352; src/app/test_daemon/light_daemon.spl:27-35,243

## Interleaving
1. Clients A and B both call ensure_daemon(); daemon_lock_alive() is false for both.
2. A: file_delete(LIGHT_LOCK), file_delete(LIGHT_BINARY), spawns daemon D1; D1 claims the lock and publishes the binary record.
3. B, slower, now runs its own file_delete(LIGHT_LOCK) and file_delete(LIGHT_BINARY), removing D1's live lock, then spawns D2. A waits for lock plus binary (40 x 50 ms) and may time out with "light daemon shell exited but did not create lock".
4. Two daemons poll the same request directory and answer the same .req files (the failure class in test_runner_concurrent_runs_lose_output_2026-08-21).

light_daemon.atomic_write_text uses the fixed name "<path>.tmp". Two daemons claiming at once both write daemon.lock.tmp; the second truncates the first's content before its rename, the loser's rename fails with ENOENT and the fallback at line 35 is a plain non-atomic file_write(path), so the lock can be observed empty or mixed. claim_lane arbitrates with a 200 ms sleep.

## Fix
Client: take an O_EXCL spawn lock, re-check daemon_lock_alive under it, and delete the lock only if the recorded pid is the one proven dead (compare-and-rename). Daemon: unique tmp name (path.pid.tmp), drop the non-atomic fallback, claim with O_EXCL or link.

## Stress spec
Launch 8 clients concurrently with no daemon; assert exactly one light_daemon remains and every client receives a verdict.

# macOS bootstrap progress must not execute setuid ps

Status: fixed; focused verification passed. No bootstrap was run for this fix.

## Failure and change

The enforced stage-2 run at `e059dd5ee2e` failed RSS observation when the
progress watcher spawned macOS `/bin/ps` (mode `4755`). The denied live PID
22253 had effective UID 0, real UID 501, and parent chain
22252 → 16616 → bootstrap 16242 → root 16241. Its PGID 16242 and SID 16241
matched the admitted workload. Omitting that process would weaken containment.
The originating evidence is
`build/evidence/macos-enforced-bd544/stage2-objcopy-e059dd5` in the restart worktree.

The watcher now obtains Darwin identity, elapsed time, CPU counters, and RSS
through `macos-process-observer.c`, using bounded sysctl/libproc requests. The
watchdog passes its admitted observer path and SHA-256 to the workload. Each
progress invocation verifies the regular file, rejects symlinks/setuid/setgid,
checks its hash, and has a five-second deadline. Standalone progress compiles
a private observer once, with a 30-second compiler deadline.

Birth identity includes microseconds. Native CPU counters use the Mach timebase
conversion required on Apple Silicon. Failed partial snapshots are discarded
and produce unknown metrics, preserving conservative stall classification.
The existing watchdog protocol, cap, ownership rules, and Linux `/proc` backend
are unchanged. Existing progress-only watcher exclusion remains unchanged;
the RSS watchdog still measures watcher descendants.

## Retained verification

Worktree: `/Users/ormastes/simple-tmp/mac-progress-no-setuid-ps-20260922`.
Raw final receipts/samples: `build/evidence/progress-no-setuid-final/`.

- `bootstrap_progress_watch_macos_test.shs`: PASS. Setuid/setgid and hash mismatch
  are rejected before exec; a `ps` sentinel is never invoked. Actual enforced
  watchdog run covers busy/idle classification, conservative first sample,
  counters/remaining counts, elapsed time, root/leaf RSS equality, and exited/stale
  reporting. Strict native compilation uses `-Wall -Wextra -Werror`.
- Watchdog: complete, 81 samples, peak 24,032 KiB; maximum sample 6.339 ms,
  maximum sample gap 110.038 ms; zero observer errors/restarts/overruns.
- Warm native snapshot mean: 19.622 ms over 20 requests, including process spawn.
  This excludes the watcher's intentional one-second CPU-baseline interval.
- Existing `bootstrap_progress_watch_tree_test.shs`: PASS on macOS (native
  nested-root and leaf samples) and Linux Docker `simple-rdoc-lane:bookworm`
  (`/proc`); shared deterministic cases cover PID reuse, failed snapshots,
  independent process-group totals, watcher exclusion, and build counters.
- `git diff --check`, working direct-env guard: PASS; executable specs under
  `doc/06_spec`: zero.

The first focused fixture exposed Mach ticks incorrectly treated as nanoseconds;
the busy-process assertion detected and prevented that false-stall regression.
Three focused verification cycles were used; the final cycle passed.

Independent review: PASS (separate reviewer, all five changed files). Path-based
execution after stat/hash validation is not an atomic defense against concurrent
same-user replacement; this fix does not claim an adversarial security boundary.

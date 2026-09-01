# `check-tree-size-push.shs` scan phase stalls for 15-20+ min — root cause: btrfs metadata-chunk exhaustion, not the script

Status: OPEN (diagnosis only — script NOT modified per instruction)
Date: 2026-08-11

## Symptom (reported)
- 16-fixture selftest completes at ~265s (matches script's documented
  measurement, `check-tree-size-push.shs:728`).
- After the selftest line, the scan phase (main loop, lines 937-951) ran
  15+ minutes on a 2-file commit with no PASS/FAIL/ERROR verdict, killed at
  ~20 min. Reproduced at reported load ~18 and again at load 51-62.

## Live evidence captured during this diagnosis
Two independent, currently-running invocations of the guard were caught
in the act:

```
pid 849186  D (disk sleep)  wchan=handle_reserve_ticket
  git -C .../simple ls-tree -r -t --name-only cc0ea5adcf55cc58ca8a36aac1df9d926fecc21b
pid 849740  D (disk sleep)  wchan=handle_reserve_ticket
  git -C .../simple ls-tree -r -t --name-only fb92cb4971f408192ae8f3b91544f2f5138af243
```

Both are inside `inspect_commit()` (`check-tree-size-push.shs:255`), the
SECOND of the two `git ls-tree` calls per commit (the `-t` listing used only
for the duplicate-entry check). Both processes are writing their output to
`$TMPROOT/lst.out` on `/tmp`, which is the same btrfs volume as `/`
(`/dev/nvme0n1p2 on / type btrfs`, `mount` confirms `/tmp` is not a separate
tmpfs).

30-second `/proc/<pid>/io` and `/proc/<pid>/stat` sampling of pid 849186:

| t | write_bytes | utime+stime (jiffies) |
|---|---|---|
| t0 | 6,586,368 | 28 |
| t0+20s | 7,241,728 | 35 |

CPU time and bytes written are both climbing — the process is making real,
if extremely slow, forward progress (~33 KB/s effective write throughput for
what should be a ~1-5 MB in-memory-speed write). This is **SLOW, not
deadlocked-hung**: no zero-progress interval was observed, and the wchan is
a real kernel wait state that resolves, not a permanent block.

## Root cause: `handle_reserve_ticket` == btrfs out of allocatable space

`handle_reserve_ticket` is btrfs's ticket-based space-reservation flush path
(`btrfs_reserve_metadata_bytes` → `btrfs_add_reserve_ticket` →
`handle_reserve_ticket`), entered whenever a metadata allocation cannot be
satisfied immediately and must wait for the filesystem to free or allocate
more space before the write can proceed. `btrfs filesystem usage /` at the
time of capture:

```
Device unallocated:   1.00MiB        <-- essentially zero headroom
Metadata,DUP: Size:51.50GiB, Used:50.97GiB (98.97%)
Data,single:  Size:3.54TiB,  Used:3.27TiB (92.47%)
```

With **1 MiB of unallocated device space** and the metadata chunk **98.97%
full**, btrfs cannot grow the metadata chunk to absorb new writes/extents. It
falls back to synchronous space reclaim (running delayed refs, forcing
transaction commits, waiting on other writers to release reservations) for
every metadata-heavy operation — exactly the `handle_reserve_ticket` D-state
observed, and exactly why a call that should take milliseconds (writing a
~10-15k-line file for a well-under-90k-file `-t` listing, smaller than the
production tree's ~112k full listing) instead crawls at tens of KB/s.

This is filesystem-level contention, **not** an algorithmic defect in the
script's scan phase. The two `git ls-tree -r [-t] --name-only` calls in
`inspect_commit()` are the only per-commit full-tree operations; there is no
`git fsck`, no O(n²) loop, and no per-path subshell in the scan loop (the
script's own comments at lines 229-236 and 273-280 document that `path_count`
/ `src_entry_count` were already converted from per-path `git ls-tree`
subprocess forks to greps over the single cached listing — that fix already
landed). Under a healthy filesystem this phase is cheap; under a
metadata-exhausted btrfs volume, every `write()` inside it can block for
seconds to minutes.

## Contributing/compounding factor: stale orphaned TMPROOT dirs

```
/tmp/tmp.* count:       589
total size:             4.1 GB
age range:               152s .. 133,684s (37 hours) old, avg ~12.7h old
processes still owning any of them: ~8 (i.e. the rest are orphaned)
```

`cleanup()` (`check-tree-size-push.shs:171-194`) removes `$TMPROOT` on EXIT,
but only runs on signals it traps (EXIT INT TERM HUP QUIT PIPE) — a
`SIGKILL` (a hard `kill -9`, or an OOM-killer strike under this same
memory/load pressure) bypasses it entirely and leaves the fixture-selftest
temp tree (16 fixtures' worth of git objects, index files, and multi-MB
`lst.out`/`sorted.out`/`dup.out` scratch files per commit inspected) on disk
permanently. With "several guard runs killed mid-flight tonight" (per the
task's own report) plus normal churn across many concurrent agent sessions
all running this same guard, hundreds of these accumulate. Each one is
itself many small files/extents — i.e. metadata pressure — so this is not
merely wasted disk space but a direct contributor to the metadata-chunk
exhaustion that is the proximate cause above. It is a vicious cycle: killed
guard runs (often killed because they were already running slow under
metadata pressure) leave debris that adds more metadata pressure for the
next run.

## Hung vs. slow — verdict

**SLOW**, confirmed by:
- steady CPU accumulation (utime+stime climbing every sample)
- steady `/proc/<pid>/io` `write_bytes` growth every sample
- `wchan=handle_reserve_ticket` is a real, resolving kernel wait (btrfs space
  reclaim), not a lock a dead peer is holding forever

Not hung: there is no zero-progress deadlock signature (no unchanging
`write_bytes`, no blocked-forever futex/mutex wait, no missing counterparty).
It is pathologically slow because the underlying filesystem has almost no
room to allocate new metadata, so `handle_reserve_ticket` must wait for
synchronous reclaim on every write instead of returning immediately.

## Proposed fix (described only — NOT applied; script left untouched)

This is a host/environment problem, not a script logic problem, so the fix
is operational, not a script edit:

1. **Immediate relief (human/ops action, not a script change):** free up
   btrfs unallocated space. `btrfs filesystem usage /` shows 1 MiB
   unallocated with the disk at 93% overall (`/dev/nvme0n1p2` 3.7T, 273G
   avail) — the *volume* isn't full, but btrfs's own chunk allocator has no
   room to grow metadata. `btrfs balance start -dusage=5 /` (or similar,
   targeted at reclaiming lightly-used data chunks back to unallocated) is
   the standard remedy; this needs a human decision since it's an
   invasive/long-running maintenance operation.
2. **Delete the 4.1 GB / 589 dirs of orphaned `/tmp/tmp.*` guard fixtures**
   from prior killed runs. This both reclaims space and directly reduces
   metadata pressure. Safe to do outside the script (`find /tmp -maxdepth 1
   -name 'tmp.*' -mmin +60 -exec rm -rf {} +`, scoped to old enough that no
   live run owns them) — this is cleanup, not a script edit.
3. **If a script change is later authorized by a human:** the existing
   `ST_CACHE_*` mechanism (lines 726-775) already avoids re-running the
   16-fixture selftest on unchanged script content, which is good, but it
   does NOT help the scan phase, which runs unconditionally. A possible
   future improvement (NOT proposed as urgent, and NOT applied here) would
   be pointing `TMPROOT` at a tmpfs-backed directory when available
   (`/dev/shm`) instead of the default `/tmp` on the same contended btrfs
   volume as the rest of the repo I/O — this would insulate the guard's own
   scratch I/O from exactly this failure mode. This is a genuine behavior
   change (moves scratch data to a size-limited tmpfs) and is flagged for
   human review, not applied.
4. Nothing about the four verification checks themselves (size band,
   duplicate-entry, src/ entry band, load-bearing floors) needs to weaken —
   this diagnosis does not implicate their design or thresholds at all.

## Files
- `/home/ormastes/dev/pub/simple/scripts/check/check-tree-size-push.shs` (read-only, not modified)

# Stage3 bootstrap memory-death plan (lane: stage3-memguard, 2026-08-18)

## Evidence
- `earlyoom -r 3600 --prefer ^(simple|rustc|cc1|...)$ --avoid ^(claude|codex|...)$` runs on this
  host (`DynamicUser` systemd unit, args from `/etc/default/earlyoom`). Userspace ⇒ **nothing in
  dmesg**. It SIGTERMs the largest `--prefer` match at ~10% free.
- Last 6h: 699 SIGTERMs at `simple`, 6 at `rustc`.
- Memory now: 125GiB total, ~19GiB available, **swap 0**.
- Each `native_build_worker.spl` peaks ~4.0GB RSS (108 reap records in `killed_seedbase.txt`, every
  victim 4.0-4.1GB, age ~60s). Concurrency × 4GB is what walks the host into the earlyoom band.
- `scripts/bootstrap/bootstrap-from-scratch.sh:2528` prints
  `warning: stage3 self-host failed (exit ${stage3_status})`. For a SIGTERM that reads
  `exit 143` — indistinguishable from a compile failure, which is exactly the wrong diagnosis.

## Decisions

### 1. bsguard.sh → do NOT promote to a repo-managed script. (ponytail rung 1)
It is a symptom mask, and a dangerous one: it `kill -KILL`s the largest >4GB process on the whole
host that isn't the bootstrap it happens to have found by `pgrep -f 'stage2-admitted/simple'`.
On a box running several lanes concurrently that reaps **another lane's** workers — the 108
recorded kills are all `/mnt/data/worktrees/simple-main/...`, i.e. cross-lane collateral. Keeping it
means institutionalising a cross-lane killer to work around a policy misconfiguration.
Keep it as a scratchpad diagnostic; retire the running instance.

### 2. Bootstrap wrapper MUST distinguish signal death. YES — implement.
Smallest correct change at `bootstrap-from-scratch.sh:2526-2529`: when `stage3_status > 128`,
report the signal number and name the likely cause, so a memory kill can never be read as a
compiler defect. ~4 lines, no new files, no new abstraction.
Applies to the strict path too (it exits with the same status) — the message is what matters.

### 3. Root fix: swap first, earlyoom policy second.
- **Swap (do this, it is the actual defect).** 128GiB RAM with **zero swap** means the kernel has no
  elastic band at all; a transient 4GB×N spike is instantly terminal. A swapfile does not need to be
  fast — it needs to exist so peaks page out instead of tripping a 10%-free trigger. This is a host
  change and therefore **requires the user's go-ahead**; it is not something this lane does silently.
- **earlyoom policy.** `--prefer simple` is correct in intent (kill the compiler, not the editor) but
  it makes the bootstrap the *designated victim* of any host-wide pressure, including pressure it did
  not cause. Options, in preference order: (a) leave policy alone and add swap; (b) raise
  `-r`/lower the trigger percentage so it fires later; (c) drop `simple` from `--prefer`, which just
  moves the kill onto something else. (a) is the only one that removes the failure rather than
  relocating it.
- **Bound worker concurrency.** Cheaper than either and complementary: the real input is
  `N_workers × 4GB`. Capping stage3 native-build parallelism against MemAvailable is the fix that
  belongs in the repo, if bsguard's job must live anywhere. Deferred — needs a measurement of the
  actual worker fan-out first; recorded here so it is not lost.

## Actions in this lane
1. Kill the three orphaned helpers (2 `tail -F`, 1 `bsguard.sh` loop) — none are load-bearing.
2. Land the signal-classification change (decision 2). Commit only, no push.
3. Report swap/earlyoom recommendation to the user; make no host changes unprompted.

## Binary identity
`bin/simple` in this worktree is a **dangling symlink** (`bin/release/<triple>/simple` absent — the
lane worktree has no deployed compiler). No stage3 run is possible here without a bootstrap first;
this lane's change is wrapper-only and does not need one.

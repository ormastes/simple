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

---

# Session handoff (2026-08-19)

## Done and VERIFIED
- **Three orphaned helpers killed** (2429872 `tail -f`, 3166117 `bsguard.sh` loop, 4145274
  `tail -F`). Verified gone by `ps` after the kill. None load-bearing.
- **Signal classification landed in `bootstrap-from-scratch.sh:2526-2536`.** `exit >128` is now
  reported as `KILLED by signal N (NAME), not a compile failure`, with a `journalctl -t earlyoom`
  hint for 15/9. Verified: `sh -n` clean; the arithmetic self-checked out of band
  (143→TERM, 137→KILL, 0/1→exit). **UNVERIFIED: the branch has never executed inside a real
  bootstrap run** — no compiler is deployed in this lane, so no stage3 was run. It is a
  message-only path, but it is untested in situ.
- **Root cause confirmed by direct observation**, not inference: `earlyoom -r 3600
  --prefer ^(simple|rustc|cc1|...)$` is live; `killed_seedbase.txt` holds 108 reaps, every victim a
  `native_build_worker` at 4.0-4.1GB, ~60s old; host is 125GiB with **swap 0**.

## Done and VERIFIED — shared-repo defect found while gating
`/mnt/data/worktrees/simple-main/.git/config:11` carries repo-wide
`core.worktree = /mnt/data/worktrees/lane-rt-bitstream`. Every linked worktree inherits it, so
`git rev-parse --show-toplevel` from ANY other lane returns lane-rt-bitstream and three guards
abort `ERROR — nothing was checked (exit 2)`. Verified by reproducing and then fixing it
scoped to this lane via `git config --worktree core.worktree`, after which the same three guards
PASS. Shared config deliberately NOT edited (another session's live tree).
Recorded in `doc/08_tracking/bug/test_tree_divergence_preexisting_stepover_2026-08-19.md`.

## OPEN — the actual blocker for the next session
**This lane cannot satisfy its own pre-push hook.** The hook runs 63 guards; **35 of them execute
the compiler** and every one fails closed here with
`ERROR — nothing was checked: compiler not executable at 'bin/simple'` (or exit 127), because
`bin/release/<triple>/` does not exist in this worktree. The first push attempt was REJECTED by
all 35 (`HTTPS_EXIT=1`, nothing landed — confirmed via `git ls-remote`, not via exit status).

Three options were put to the user and **none was chosen** (no reply received):
1. symlink `bin/simple` at simple-main's deployed binary (59645008 bytes, 2026-08-18 10:12) —
   cheap, guards genuinely run, but gates this push on another lane's build;
2. bootstrap a compiler in this lane — correct, and walks straight into the earlyoom death this
   very commit is about;
3. `--no-verify` plus a tracking record, as in `f0f5c5d1a70`.
Recommendation stands at (1). **Next session should resolve this first** — it blocks any push
from this lane, not just this change.

## OPEN — unfixed, and NOT this lane's to fix unilaterally
- **swap 0 on a 125GiB host** is the real defect. Needs the user's go-ahead; no host change was made.
- **Worker concurrency is unbounded** against MemAvailable; `N × 4GB` is the actual input to the
  failure. Deferred, needs a fan-out measurement.
- **854-entry test-tree divergence backlog** on main, owned by earlier sessions.
- **`check-no-direct-rt` baseline drift** (measured 18578 vs baseline 18788, and separately
  12012→12020 upstream) — smells like lanes landing without full gates. Not investigated.

## Honest notes on process
- Two self-inflicted errors this session: a `pkill -f` whose pattern matched its own shell (killed
  the push before it ran), and a foreground `git push` that hit the 2-minute tool timeout mid-flight.
  Both were caught only because the remote was re-checked with `git ls-remote` — the exit codes
  alone would have read as success. Re-verify the remote after every push; do not trust exit status.
- Origin moved four times during this session (`ca7c33ecf75` → `38df765fb253` → `e347858a954` →
  `abb8cd08428`). Guard results have a shelf life of minutes here; run them immediately before push.

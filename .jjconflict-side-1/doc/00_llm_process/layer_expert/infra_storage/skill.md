# Layer Expert — Infra / Host Storage

## Scope

Host-level storage that every other layer silently depends on: the btrfs root,
the ext4 scratch volumes, worktree placement, `TMPDIR`, Docker `data-root`, and
QEMU image locations. This layer has no product code — it exists because its
failures are routinely **misattributed to the compiler, the gates, or the
guards**.

## The one thing to know

On a btrfs volume, `df` reporting free space does **not** mean writes will
succeed. When `Device unallocated` reaches zero, metadata cannot grow and the
filesystem returns `ENOSPC` with hundreds of GB "free".

```bash
btrfs filesystem usage / | grep -iE 'unallocated|Metadata,DUP'
```

`Device unallocated: 1.00MiB` + `Metadata,DUP: 98.98%` = the volume is failing,
whatever `df` says.

## Misattribution table

Every row below was diagnosed as a distinct product bug on 2026-08-10/11 before
the common cause was found. All are one fault.

| Observed | Wrongly attributed to | Actually |
|----------|----------------------|----------|
| Guards run for minutes, no verdict line | Guard scripts being slow/hung | metadata stall |
| `git write-tree` times out on 2 files | git corruption, index lock | metadata stall |
| Kernel build exceeds 900s ceiling | compiler perf regression | metadata stall |
| `wm-simple-web-build-timeout` on WM gate | SimpleOS rung-(d) defect | metadata stall |
| Load average >70 | too many concurrent agents | D-state on `handle_reserve_ticket` |
| Agent harness cannot write output files | tooling/harness bug | metadata stall |

**Rule: before filing a perf or timeout defect, check `btrfs filesystem usage`.**
A timeout on a starved volume is not evidence about the product.

## Recovery order (getting this wrong wastes hours)

1. **Delete or migrate real data.** Whole chunks must empty.
2. **Then** `sudo btrfs balance start -dusage=5 /`, escalating to `10`, `20`.
3. Confirm `Device unallocated` actually grew.

`balance` first **fails with ENOSPC** — it needs free space to relocate into.
This was attempted and failed; do not repeat it.

## What fills this host

Git worktrees, not build artifacts. 279 registered worktrees at ~109k files
each. `git worktree prune` reclaims almost nothing (2 of 279) because they are
live registrations. Worktrees belong on `/mnt/data`.

## Migration method

Copy → delete original → symlink the original path to the new location. Path
preservation keeps git worktree metadata valid, so `git worktree repair` is not
needed. Verify the result with `ls -ld` — a script still on an earlier step
looks exactly like one that finished.

## Never delete another session's scratch

Per-session dirs under `/tmp/claude-1000/` can exceed 100 GB. A parent-directory
mtime cutoff **does not** tell you whether a session is live. Check per-file
recency:

```bash
find <session-dir> -mmin -60 -type f | wc -l   # >0 means ACTIVE — do not delete
```

Measured: two sessions holding 135 GB and 51 GB were both live despite looking
stale by directory mtime. Purging on the naive cutoff reclaimed 8 GB, not the
190 GB projected.

## Links

- `doc/07_guide/infra/host_storage_layout.md` — volumes, fstab, full procedure
- `.claude/skills/spipe.md` § Host storage precondition
- `.claude/rules/commands.md` — fast path and measurement discipline

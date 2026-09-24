# Host Storage Layout and the btrfs Metadata Exhaustion Trap

Established 2026-08-11 after a full-night outage in which every gate, guard, and
build on this host failed or timed out for a single root cause that presented as
a dozen unrelated symptoms.

## Volumes

| Mount | Device | Size | FS | Purpose |
|-------|--------|------|----|---------|
| `/` | `nvme0n1p2` (Samsung 990 PRO 4TB w/ heatsink) | 3.7 T | btrfs | System + repo. **Keep below ~85%.** |
| `/mnt/data` | `nvme2n1` (Samsung 990 PRO 4TB) | 3.6 T | ext4 | Worktrees, temp, QEMU images, Docker data-root |
| `/mnt/fast` | `nvme1n1` (SAMSUNG MZQL2960HCJR) | 894 G | ext4 | Secondary scratch (datacenter endurance) |

Both scratch volumes are in `/etc/fstab` by UUID with `noatime,nofail`.

## The trap: ENOSPC with hundreds of GB free

btrfs allocates disk in **chunks**, separately for data and metadata. When every
chunk is allocated, metadata cannot grow **even though `df` reports free space**,
because that free space sits *inside* data chunks. The volume then fails writes
with `ENOSPC` while showing ~275 GB available.

Diagnose with `btrfs filesystem usage /`, never `df`:

```
Device unallocated:      1.00MiB      <-- the actual fault
Data,single:  Size:3.54TiB, Used:3.27TiB (92.42%)
Metadata,DUP: Size:51.50GiB, Used:50.97GiB (98.98%)
Free (estimated): 274.70GiB           <-- misleading; df agrees and is wrong
```

`Device unallocated` near zero + metadata >95% is the signature.

### Symptoms it produces (all observed in one night)

- Pre-push guards run for minutes and never emit a verdict line
- `git write-tree` times out on a two-file commit
- A 1512-file kernel native build exceeds a 900s ceiling (`wm-simple-web-build-timeout`)
- `du` on a few directories exceeds 180s
- Load average >70 with idle CPUs — processes are in **D state** on
  `wchan=handle_reserve_ticket`, not computing
- Agent harnesses fail to create their own output files; tooling appears broken

Every one of these reads as a distinct bug. They are one fault.

### Why `btrfs balance` is NOT the first move

**`balance` cannot rescue a volume this full — it fails with ENOSPC itself.**
Balance relocates extents out of sparse chunks into free space; with data chunks
at 92% full, almost nothing qualifies and there is nowhere to relocate into.

```
ERROR: error during balancing '/': No space left on device
```

Correct order:

1. **Delete or migrate real data** until whole chunks empty out.
2. **Then** `sudo btrfs balance start -dusage=5 /`, escalating to `-dusage=10`,
   `-dusage=20` as headroom appears.
3. Verify with `btrfs filesystem usage /` that `Device unallocated` actually grew.

A `-dusage=5` pass on a 3.6 TB volume found only 5 qualifying chunks — enough to
break the deadlock briefly, not enough to fix it.

## What actually fills this host

Not build artifacts. **Git worktrees.** Measured 279 registered worktrees at
~109,000 files each, spread across:

| Location | Count |
|----------|-------|
| `/tmp` | 117 |
| `/home/ormastes/dev/pub` (`simple-*`) | 101 |
| `.claude/worktrees` | 45 |
| other | 16 |

`git worktree prune` reclaimed only 2 — these are live registrations, not debris.
Worktrees belong on `/mnt/data`, never on `/`.

## Migration method: symlink, do not reconfigure

Copy the directory to the scratch volume, delete the original, and symlink the
original path to the new location. **Because the path is preserved, git worktree
metadata (`.git` gitdir pointers and `.git/worktrees/<name>`) stays valid and
`git worktree repair` is unnecessary.**

```sh
cp -a .claude/worktrees/. /mnt/data/worktrees/
rm -rf .claude/worktrees
ln -s /mnt/data/worktrees .claude/worktrees
```

Verify the result is actually a symlink (`ls -ld`) before believing it — a script
that is still on an earlier step looks identical to one that finished.

### Known limits of this approach

- **Claude worktrees**: `.claude/worktrees` is a fixed path; the symlink is the
  only lever. There is no config key.
- **Codex worktrees**: `~/.codex/config.toml` has **no worktree/tmp/dir key**.
  Symlinking existing worktrees works, but *new* Codex worktrees land wherever
  the invoking agent chooses — usually `/`. The only durable fix is making
  `/home/ormastes/dev/pub` itself resolve to `/mnt/data`.
- **`TMPDIR=/mnt/data/tmp`** in `~/.bashrc` catches `/tmp`-based scratch for both
  tools in new shells only.

## Docker

`data-root` moved to `/mnt/data/docker` via `/etc/docker/daemon.json`. Requires
stopping the daemon (running containers stop). Keep the old tree as
`/var/lib/docker.old` until the new root is confirmed, then reclaim.

## Do not delete another session's scratch

`/tmp/claude-1000/<project>/<session>/` can hold >100 GB per session. Before
deleting, check the directory for files modified in the last hour AND count live
processes:

```sh
find <session-dir> -mmin -60 -type f | wc -l    # >0 means ACTIVE
pgrep -af claude | wc -l
```

Measured 2026-08-11: two sessions held 135 GB and 51 GB and were **both live**.
A 24-hour mtime cutoff on the parent directory classified them as stale; only the
per-file recency check revealed they were running. Purging 58 of 63 session dirs
on that cutoff reclaimed just 8 GB — the volume was in the active sessions.

## Operating rule

**Check `btrfs filesystem usage /` before starting any long gate, bootstrap, or
evidence run.** If `Device unallocated` is under ~5 GiB, stop and reclaim space
first. A run started on a starved volume produces timeouts that are
indistinguishable from real product defects, and every hour spent debugging them
is wasted.

See also: `.claude/rules/commands.md` (fast path), `.claude/skills/spipe`
(host preconditions).

## Worktrees fill disks too — not just session dirs (2026-09-12)

The round-2 macOS open-bugs fix pass ran ~30 parallel agent worktrees under
`.claude/worktrees/` in one day and filled a 460 GB disk. Each worktree is a
full checkout plus its own `build/` artifacts — `build/` is **not shared**
across worktrees (it is untracked, per-worktree state, same as any other
uncommitted directory), so N worktrees running a bootstrap or cargo build pay
the disk cost N times over, not once.

Mandatory hygiene for anyone spawning worktree-based agent lanes:

- **Remove a worktree as soon as its PR lands.** A merged worktree is dead
  weight from that point on — `git worktree remove <path>` (or `rm -rf` the
  directory if the worktree was already force-removed) immediately after
  `gh pr merge` confirms the merge landed, not at end-of-session cleanup.
- **`git worktree prune` after manual removal.** Deleting a worktree directory
  by hand leaves a stale admin entry under `.git/worktrees/`; prune it so
  `git worktree list` reflects reality and future `add` calls don't collide.
- **Never assume `build/` is shared.** If a lane needs a prebuilt seed or
  cargo target, copy it in explicitly (`cp -Rc` on macOS APFS for
  copy-on-write, per the 09-06 macOS-bootstrap memory note) — don't rely on a
  sibling worktree's `build/` being visible or reusable in place.
- **Check `df -h` / `btrfs filesystem usage /` before AND during a
  many-worktree fan-out**, not just before a single long gate run (see
  Operating rule above) — the failure mode here is cumulative across many
  short-lived worktrees, not one long-running process.

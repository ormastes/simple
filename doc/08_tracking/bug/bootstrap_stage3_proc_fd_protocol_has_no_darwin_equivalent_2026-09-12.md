# Stage-3 provenance uses a `/proc/<pid>/fd` protocol with no darwin equivalent (2026-09-12)

Status: OPEN. Scope corrected — this is NOT the "19 `/proc` refs in one file"
item it has been tracked as for two rounds
(`doc/03_plan/infra/macos_open_bugs_fix_lanes_round2_2026-09-12.md`, lane 1).

## What the 19 references actually are

`scripts/check/lib/bootstrap-stage3/manifest-verify.shs` carries 19 `/proc`
references in three distinct categories, not one:

| category | lines | what it needs |
|---|---|---|
| status-fd write | 3 (`/proc/self/fd/159`) | write to an inherited fd by path |
| own pid without forking | 8 (`/proc/self/stat`) | the caller's pid |
| **unlink-then-read-by-fd-path** | 35, 41, 57, 115-120, 137-189, 376-381 (17 refs, fds 6/7/8/9) | a TOCTOU-proof *re-readable path* to a file that has been `rm`'d after opening |

Only the first two are the "host probe" shape the plan record assumed. The
third is the substance, and it is a **cross-file protocol**, not a local idiom:
`authority.shs` (:160, :225, :1769-1795, :2214, :2405), `manifest-write.shs`
(:7, :9, :19, :59) and `command-snapshot.shs` (:113-115) all *validate* paths
against the literal pattern `/proc/[1-9][0-9]*/fd/[1-9][0-9]*`, and
`authority.shs:179-180` additionally reads `/proc/<pid>/stat` field 20 for a
start-time identity. Any port has to move all of them together or the
fail-closed pattern arms reject the new spelling.

## Why `/dev/fd/N` is NOT the darwin equivalent (measured, this host)

The obvious substitution is wrong, and it fails *silently* in the direction that
looks like a provenance failure rather than a portability one. On Linux
`/proc/self/fd/N` is a magic symlink, so each open is a fresh `open()` at offset
0. On macOS `/dev/fd/N` is `fdesc`, whose open is a **dup** — the offset is
shared, so the second read of the same view sees EOF:

```
$ printf 'a\nb\nc\n' > t.txt; exec 7<t.txt; rm -f t.txt
$ wc -l </dev/fd/7   -> 3
$ wc -l </dev/fd/7   -> 0        # Linux would print 3 again
$ sed -n 1p /dev/fd/7 -> (empty)
$ [ -f /dev/fd/7 ]    -> true    # so the guard's -f arm passes and hides it
```

`bootstrap_stage3_verify_manifest_impl` reads its bound map at least four times
(`schema`, `status`, `entry_count`, the `sed` role scan, `wc -l`, `tail -n +5`).
With `/dev/fd` the first read succeeds and every later one returns empty, so the
run dies at `manifest-stage-map-schema` — fail closed, correct, and completely
misleading about the cause.

## What a real port needs

- Feature-detect **procfs**, not `uname`: FreeBSD (the QEMU bootstrap lane) has
  no `/proc` either, so a `case darwin` port leaves that lane broken.
- One seam, e.g. `bootstrap_stage3_fd_view <fd> <snapshot_path>`, returning
  `/proc/$pid/fd/N` (caller `rm`s, today's behaviour byte-identical) when
  `[ -r /proc/self/stat ]`, and otherwise the snapshot path itself — kept
  **linked** in a `mkdtemp` 0700 dir, `chmod 0400`, removed on an exit trap.
  That is a genuinely weaker anti-TOCTOU guarantee than unlink-by-fd and the
  port must say so rather than imply parity.
- The pattern arms in `authority.shs` / `manifest-write.shs` /
  `command-snapshot.shs` must accept the non-procfs spelling, or the port is
  rejected by its own siblings.
- Categories 1 and 2 are cheap and independent: `/proc/self/fd/159` -> `/dev/fd/159`
  (dup semantics is fine for a write), and `/proc/self/stat` -> `$(sh -c 'echo $PPID')`
  keeping the existing positive-integer fail-closed check.
- **Selftest discriminator:** the fixture must perform **three or more
  sequential reads of the same view**. A single-read fixture passes on the
  broken `/dev/fd` port too, which is exactly how this would land green and
  still not work.

## Why it was not done in this pass

The change is a security-critical provenance protocol spanning four files and
~3,000 lines, and the Linux arm cannot be exercised from this host. Landing an
untestable partial port of a fail-closed authority chain is worse than landing
the measurement. The `/dev/fd` probe above is the part that was missing.

Related, and fixed in the same PR: the stale-ownership-lock half of lane 1 —
`scripts/check/lib/portable-hardlink-lock.pl` read its process table only from
`/proc`, so `refine_leader_group_state()` took its documented "macOS opts out"
path. Now falls back to `ps -axo pid=,ppid=,pgid=,lstart=`, pinned by
`scripts/check/check-portable-lock-dead-owner-reclaim.shs`.

# Bootstrap progress watcher reports only wrapper RSS

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Fixed for future canonical runs. The active canonical run was not restarted or
modified.

## Measured defect

Canonical source `71ebd8dae6c0` launched
`scripts/bootstrap/bootstrap-from-scratch.sh` as PID 3554675. At 121 seconds,
`bootstrap-progress.log` reported `rss_kb=2600`, the shell wrapper alone. At the
same instant, the wrapper plus its build descendants consumed approximately
7,708 KiB after excluding the watcher subtree: 2.96 times the recorded value.
The process had not yet launched a compiler, so the same root-only sample would
hide nearly all RSS once Stage 2, Stage 3, or Stage 4 consumed GiB.

Cycle 2 reproduced the gap: at process elapsed 2:17, root PID 3879774 used
2,596 KiB while the root and build-side descendants used 7,692 KiB after the
existing watcher was excluded, again 2.96 times the recorded value.

The cause was a single `ps -p "$watch_pid"` query. Child compilers are launched
beneath that PID but were never included.

## Fix

Keep the existing `pid`, `cpu_pct`, and `rss_kb` root-process fields unchanged.
Add transitive `tree_cpu_pct`, `tree_rss_kb`, and `tree_processes` fields from
one process-table snapshot per interval. Exclude the watcher and all of its own
descendants so monitoring overhead is not charged to the compiler tree.

Tests cover an exact two-process nested tree, an adjacent leaf with identical
root/tree RSS, and an already-exited PID retaining the prior terminal format.

## Next measured bottleneck, not changed here

Cycle 1 remained at the `starting` milestone for 197 seconds and then failed
admission because the clean worktree lacked the ignored Rust seed/runtime
authority; no compiler stage launched. At 155 seconds, its active build-side
descendant was still the per-file fingerprint/source-authority shell chain.
That prebuild latency is separately measurable, but source and tool authority
are admission inputs. It must not be shortened by dropping hashes or snapshots;
this fix deliberately does not change it.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN, fix claim remains unverified.** A content grep for 'watcher|rss' in
`scripts/bootstrap/bootstrap-from-scratch.sh` returns 1 incidental hit and no child-tree RSS
aggregation, so the doc's own admission (canonical run never restarted, fix unverifiable) holds.
NOT proven either way this session: no bootstrap was run, per lane host-etiquette rules.

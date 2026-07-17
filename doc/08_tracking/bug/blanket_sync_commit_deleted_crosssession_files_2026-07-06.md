# Blanket "sync working changes" commit deleted another session's files

## Status
**RESOLVED** — Recovered (2026-07-06; triage-confirmed 2026-07-17: all 4 files verified present on disk, deleting commit 620fc04479e6 confirmed via `git log`). 3 of 4 files restored by this record's fix; the 4th
(the parity harness spec) was restored concurrently by a different session —
see Files Deleted below for the split.

## Severity
High — one of the deleted files was a bit-exact test harness gating a landed
refactor (`c8ac6e4360`), so the gate was silently absent from origin `main`
until noticed and restored.

## Summary
Commit `620fc04479e6` ("chore: sync working changes", already pushed to
origin before discovery) accidentally **deleted 4 files** that a different,
concurrently-running agent session had just created in the same shared
working copy:

- `doc/01_research/ui/rendering/draw_ir_multibackend_research.md`
- `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md`
- `doc/05_design/ui/rendering/draw_ir_multibackend_design.md`
- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`

All four files had been created/corrected moments earlier by commit
`d2cd221f` ("docs(design): correct Draw-IR multibackend design per
verification+audit — op/stub counts, mixin infeasible→FR-RENDER-MIXIN,
bit-exact harness gate, honesty debt") and a companion harness-authoring
change. `620fc04479e6` was authored by a peer session that ran a broad,
undifferentiated working-copy snapshot commit — it captured the deletion as
part of "whatever the working copy currently looks like" rather than a
deliberate, scoped change.

## Root Cause
Multiple agent sessions operate against the **same jj working copy**
concurrently (see `.claude/memory/reference_jj_push_concurrent_agents.md`).
One session ran a blanket `jj commit` (no path scoping) to "sync working
changes" at a moment when, from that session's point of view, the four files
above did not exist yet in its own snapshot lineage / had been locally
removed by an unrelated operation in its lane. Because the commit was
unscoped, it committed that absence as a deletion, and the commit was then
pushed to origin, propagating the deletion to `main` for every other session
and any fresh checkout.

This is a **process/coordination bug**, not a code bug: jj's working-copy
model correctly recorded what was on disk at commit time; the failure is
that a peer trusted a blanket snapshot commit to be safe in a shared,
multi-session working copy, when in fact any concurrently-created file not
yet visible/settled in that session's view is at risk of being recorded as
deleted.

## Impact
- The bit-exact parity harness (`engine2d_shared_raster_parity_spec.spl`)
  that validates the landed P1 engine2d shared-raster refactor (`c8ac6e4360`)
  was absent from origin `main` HEAD from the time `620fc04479e6` landed
  until it was restored — i.e. the refactor's regression gate did not
  actually exist on the branch of record for that window.
- Two design/planning docs (research + plan) that recorded a corrected,
  verified analysis (op counts, `FR-RENDER-MIXIN` deferral rationale, honesty
  debt audit) were also gone from origin, along with the design doc itself.

## Recovery
Each file was restored from the last commit that had it, using the parent of
the deleting commit:

```
jj restore --from 620fc04479e6- <path>
```

- `doc/01_research/ui/rendering/draw_ir_multibackend_research.md` — restored
  from `620fc04479e6-`; content verified **byte-identical** to the corrected
  `d2cd221f` version (diff empty).
- `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md` — restored from
  `620fc04479e6-`; content verified **byte-identical** to the corrected
  `d2cd221f` version (diff empty), including `FR-RENDER-MIXIN` deferral and
  the corrected 28-op count.
- `doc/05_design/ui/rendering/draw_ir_multibackend_design.md` — restored and
  extended by a separate concurrent session (not this record's work).
- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` —
  restored by a separate concurrent session in parallel with this record
  (explicitly out of scope for this fix to avoid a collision on the same
  file).

Note: `jj restore --from <rev>` on a stale/shared working copy can leave the
in-memory working copy out of sync with disk immediately afterward (`jj
status` shows the restored file as `A`, but `ls` reports it missing); running
`jj workspace update-stale` reconciled the divergence and materialized the
files on disk in this recovery.

## Prevention / Lessons
- **Do not trust a peer session's blanket "sync working changes" commit to
  preserve files created by other concurrent sessions.** A commit with no
  path arguments snapshots the *entire* working copy as that session sees
  it, including any deletions the acting session's own operations (or a
  stale view) introduced — even for paths it never intentionally touched.
- **Prefer scoped commits**: `jj commit <path> <path> ...` for any change
  landed while other sessions may be concurrently active in the same working
  copy. This is already policy (see `.claude/rules/vcs.md` root-first rebase
  guidance) but bears repeating specifically for the "sync working changes"
  pattern, which by construction has no path scoping.
- **After any peer sync lands on origin, spot-check that critical files
  (test gates, specs, freshly-added docs) still exist** before assuming the
  sync was a no-op for your lane. A quick `git show <sha> --stat` on the
  peer's commit reveals unexpected deletions before they propagate further.
- **Test gates are especially fragile in this failure mode**: a deleted spec
  file doesn't fail loudly — it just stops being run, so the absence of a
  test result can look identical to "nothing changed" rather than "gate
  vanished." Treat unexplained drops in test count from a session's own
  runs as a signal to diff the spec directory against origin, not just
  re-run.

## Related
- `.claude/memory/reference_jj_push_concurrent_agents.md` — general
  concurrent-jj-session guidance (stale workspace, rebase races).
- `doc/05_design/ui/rendering/draw_ir_multibackend_design.md` — companion
  design doc restored by a parallel session.
- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` —
  companion harness spec restored by a parallel session.

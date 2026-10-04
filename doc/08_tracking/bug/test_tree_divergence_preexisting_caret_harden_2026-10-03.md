# Test-tree divergence: pre-existing offenders at the caret-harden landing (2026-10-03)

Landing `work/caret-suite-harden-20261003` on a delta-PASS, as
`.claude/rules/vcs.md` requires this record.

- Base: `88ecaa21054` (origin/main). Head: the branch tip.
- `sh scripts/check/check-test-tree-divergence-delta.shs 88ecaa21054 HEAD`
  -> `PASS — 3140 pre-existing offender(s), 0 introduced by this range` (80 s).
- Base verdict: `FAIL — 3806 diverged vs 965 baselined (2973 new, 132
  fixed-but-still-baselined); 36 mirror-only (35 unallowlisted)`.
- The offender list (3806 lines) is reproducible byte-for-byte by rerunning the
  command above against the same base; it is not copied here.

This branch edits one already-diverged pair on the `test/01_unit` side only
(`os/apps/smux/smux_app_spec.spl`) and adds specs with no `test/unit` twin.

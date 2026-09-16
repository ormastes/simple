# Pre-existing test-tree divergence recorded at PR #235 landing (2026-09-01)

Required by `.claude/rules/vcs.md` — landing on a divergence-delta PASS
REQUIRES recording the pre-existing offender list. An unrecorded step-over is a
violation even when the delta is clean.

## Verdict at PR #235 tip `f9c660acff6`

```
check-test-tree-divergence-delta: base verdict: check-test-tree-divergence: FAIL — 3955 diverged vs 965 baselined (3085 new, 95 fixed-but-still-baselined); 26 mirror-only (25 unallowlisted, 0 stale-allowlist)
check-test-tree-divergence-delta: PASS — 3205 pre-existing offender(s), 0 introduced by this range
```

Run independently of the authoring lane, `origin/main..pr235`, committed
content via `--ref` on both sides (never the shared working copy, which
disagrees under concurrent load).

## Scope of this record

The 3,205 offenders are a PRE-EXISTING backlog left by earlier sessions, NOT
introduced by #235. #235 initially introduced 6 new divergences; those were
resolved per-file (both directions diffed) before landing, and a re-run found
and removed 2 further orphaned mirror twins. The full offender list is at
`/mnt/data/tmp/test_tree_divergence_preexisting.txt` as emitted by the helper.

The backlog itself remains open and is not addressed here.

# Test-tree divergence step-over record — 2026-08-18 (lane test-fix)

**Status:** OPEN (unverified 2026-09-12)

`check-test-tree-divergence.shs --ref HEAD` is RED on `origin/main` independently
of this lane:

```
check-test-tree-divergence: FAIL — 855 diverged vs 854 baselined (1 new, 0 fixed-but-still-baselined); 2 mirror-only
```

Per `.claude/rules/vcs.md` the scoped-delta escape was used, and it is clean:

```
check-test-tree-divergence-delta: pre-existing red is identical at BASE and NEW; this range introduces nothing
check-test-tree-divergence-delta: PASS — 1 pre-existing offender(s), 0 introduced by this range
```

BASE `origin/main` -> NEW `HEAD`. This lane's range touches only
`src/compiler_rust/compiler/src/{interpreter/expr.rs,interpreter_state.rs,interpreter/mod.rs}`
and adds two specs under `test/shared/types/`, a directory with no mirror tree,
so it cannot move the divergence count either way.

The step-over is RECORDED as the rule requires; it is **not** a fix. The full
pre-existing offender list (855 entries) is saved alongside this record at
`test_tree_divergence_preexisting_2026-08-18.txt`.

The other seven mandatory pre-push guards all passed on this range:
conflict-tree, conflict-markers, tree-size, seed-build, runtime-API,
C-runtime, and the delta helper above.

## Still open
The 1 unbaselined new divergence and the 2 mirror-only entries are owned by
whichever lane introduced them; this record only documents that this lane did
not add to them.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.

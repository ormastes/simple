# Test-tree divergence step-over record — 2026-08-18 (lane test-fix)

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

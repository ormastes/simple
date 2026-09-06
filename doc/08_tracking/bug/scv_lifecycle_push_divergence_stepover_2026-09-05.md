# Step-over record: pre-existing test-tree divergence at the Stage 0.5 push

**Date:** 2026-09-05
**Range landed:** `e0432cd7be2..db6350534b4` (7 commits, Stage 0.5 source-complete)

`.claude/rules/vcs.md` permits landing over a pre-existing test-tree divergence
red ONLY on a mechanical delta-PASS, and REQUIRES recording the pre-existing
offender list. This is that record. An unrecorded step-over is a violation even
when the delta is clean.

## Verdicts

```
check-test-tree-divergence (base e0432cd7be2)
  FAIL — 3955 diverged vs 965 baselined (3085 new, 95 fixed-but-still-baselined);
         26 mirror-only (25 unallowlisted, 0 stale-allowlist)

check-test-tree-divergence-delta e0432cd7be2 db6350534b4
  PASS — 3205 pre-existing offender(s), 0 introduced by this range
```

The base red is inherited from `origin/main`, not created here. This range
introduces **zero** new divergence: it touches no file in either duplicated test
tree (`test/01_unit` vs `test/unit`, `test/02_integration` vs `test/integration`).

Offender list retained beside this record as
`test_tree_divergence_preexisting_2026-09-05.txt` (3,205 entries).

## Other push-tier guards on the same range

| guard | verdict |
|---|---|
| `check-no-conflict-tree-push` | PASS — 7 commits, 7 unique trees, 0 conflict trees |
| `check-no-conflict-markers-push` | PASS — 28 files scanned, 0 markers |
| `check-tree-size-push` | PASS — 7 commits banded, base 133,638 files, 0 structural faults |
| `check-c-runtime-compiles-push` | PASS — 126 files compiled, 0 errors (5 external-SDK skips) |

## Not run, and why

`check-seed-builds-push.shs` — this range touches no Rust or C source
(`src/compiler_rust/**`, `src/runtime/**` untouched), and a cold `cargo check`
exceeds the interactive budget on this host. Recording the omission rather than
implying coverage.

The divergence backlog itself is not this lane's to fix and is untouched here.

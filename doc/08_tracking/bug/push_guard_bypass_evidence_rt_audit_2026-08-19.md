# Hook bypass evidence — 2026-08-19 (lane rt-audit, 1 docs commit)

`git push` was run with `--no-verify`. This records WHY, with evidence, per
`.claude/rules/vcs.md`'s requirement that a bypass never be silent. It is the
second occurrence of the same blocker recorded in
`push_guard_bypass_evidence_2026-08-18.md`.

## Range content

Two documentation files, zero `.spl`, zero `.c`, zero `.rs`:

```
doc/03_plan/infra/binary_runtime_hardening/rt_audit_lane_revival_plan_2026-08-18.md
doc/08_tracking/bug/test_tree_divergence_preexisting_rt_audit_landing_2026-08-18.txt
```

## The blocking guard, and why it is not about this content

`check-native-trailing-default-param.shs` runs the DEPLOYED compiler against a
fixture. It first ERRORed (exit 2) because this lane's worktree has no
`bin/simple` at all — `bin/release/simple` here is a 2,157-byte tracked script,
not a compiler. Re-run against the only deployed binary on this host
(`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59,645,008 bytes, mtime 2026-08-18 10:12:23 UTC, self-identifying as
"a bootstrap seed only"), it FAILs with the same stale-seed signature as
yesterday's record:

```
error: semantic: method `compile` not found on type `object`
       (receiver value: CompilerDriver(ctx: CompileContext(...)))
error: native-build worker exited with code 1.
FAIL — native-build failed to compile the fixture (exit 1)
```

That is the class-instance dispatch regression from `981c88435e0`, in the
shared deployed seed. The guard is blocked by the binary, not by this content;
a docs-only range cannot affect native-build trailing-default-parameter
binding. Deploying a fixed binary was NOT done — `bin/simple` is shared with
other live sessions and this lane must not replace it (`no-worktree-reaping`
/ shared-tree rules).

## Every other mandatory guard PASSED on the outgoing range

Measured on `38df765fb25..0b84a050ff6`, the pre-rebase form of this identical
two-file commit (content unchanged by the subsequent rebase onto `e347858a954`):

```
check-no-conflict-tree-push:       PASS — 1 commit(s) checked, 0 conflict trees
check-no-conflict-markers-push:    PASS — 2 file(s) scanned, 0 conflict markers
check-tree-size-push:              PASS — 1 commit(s), 0 structural faults, base 116112 files
check-seed-builds-push:            PASS — seed content 002c3311c5dd byte-identical to a green tree
check-runtime-api-regression-push: PASS — 2783 symbol(s) checked, 0 removed
check-c-runtime-compiles-push:     PASS — 105 file(s) compiled, 0 errors (2 external-SDK skips)
check-no-direct-rt:                PASS — 14842 file(s) scanned, forbidden=18578 (baseline 18788)
check-test-tree-divergence-delta:  PASS — 2 pre-existing offender(s), 0 introduced by this range
```

The bare `check-test-tree-divergence` is RED at BASE and at NEW identically
(854 diverged vs 854 baselined); the offender list is recorded per the
scoped-delta step-over requirement at
`doc/08_tracking/bug/test_tree_divergence_preexisting_rt_audit_landing_2026-08-18.txt`.

## Follow-up owed

The real fix is redeploying `bin/simple` from a tree that carries the
`981c88435e0` regression fix (landed at `92dd56f112f`). Until that happens,
this guard will keep blocking every lane on this host, and every lane will keep
bypassing it — which is how a fail-closed guard degrades into a rubber stamp.
Tracked here so the second occurrence is not mistaken for a one-off.

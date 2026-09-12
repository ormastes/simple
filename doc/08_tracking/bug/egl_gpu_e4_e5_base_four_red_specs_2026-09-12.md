# Four EGL specs are RED at Codex's `gpu-e4-e5` base and land red with it (2026-09-12)

- Status: OPEN (2026-09-12)
- Component: `src/app/cli/environment_variant_startup_owner_v1.spl`,
  `src/compiler/00.common/structural_contracts/environment_variant_policy_handoff_v1.spl`,
  `src/compiler/10.frontend/environment_variant_frontend_policy_binding_v1.spl`,
  `src/lib/nogc_sync_mut/composition/environment_variants/feature_registry_v1.spl`
  (and their specs) — all authored by Codex on
  `codex/gpu-e4-e5-production-sol-20260912`
- Impact: four specs land non-green on `main` with the EGL wave PR. They are
  carried, not caused, by that PR.
- Owner: the Codex `gpu-e4-e5` lane. That session hit its usage limit, which is why
  its branch is being landed by someone else and why these are filed rather than
  fixed here — fixing another lane's semantics blind is how a carrier turns into a
  clobber.

## Verdicts, on the branch being landed

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50093192 bytes, 2026-09-06 09:59:11 +0900 (deployed Rust seed), sha256 `3d120a6f…`.

```
test/01_unit/app/cli/environment_variant_startup_owner_v1_spec.spl
  outcome=ERROR declared>=8 executed=8 passed=5 failed=3 skipped=0 dropped=0
  semantic: undefined field: unknown property or method 'not' on String
test/01_unit/compiler/common/environment_variant_policy_handoff_v1_spec.spl
  declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=parse-error
  parse: expected Comma, found Val
test/01_unit/compiler/frontend/environment_variant_frontend_policy_binding_v1_spec.spl
  outcome=ERROR declared>=6 executed=6 passed=3 failed=3 skipped=0 dropped=0
  semantic: undefined field: unknown property or method 'not' on String
test/01_unit/lib/nogc_sync_mut/composition/environment_variants/feature_registry_v1_spec.spl
  outcome=ERROR declared>=5 executed=5 passed=4 failed=1 skipped=0 dropped=0
  semantic: variable `available` not found
```

## Pre-existing, measured rather than assumed

The same four specs were run in a detached worktree at **`bd8df49e8d4`** — the EGL
core base, i.e. Codex's 24 commits merged onto gate-sync `main`, before any Claude
agent commit and before the `origin/main` merge — on the same binary. The four
verdict lines come back **byte-identical** to the four above: 5/8, parse-error,
3/6, 4/5.

So nothing in the nine agent commits, the U2/X2/V2 follow-ups, the `origin/main`
merge, or the `rt_*` rewiring moved them. In particular the `rt_*` rewiring is
separately clean: `test/01_unit/compiler/driver/host_environment_snapshot_v1_spec.spl`,
the spec for the file whose four `extern fn rt_*` declarations were replaced by
`std.sffi.host` aliases, is **12/12 PASS**.

## What the failures look like from outside the lane

Two of the three semantic failures are the same shape — `'not' on String`, i.e.
a `.not` reached on a value the interpreter sees as text rather than bool — which
suggests one defect with two call sites rather than three independent ones. The
parse-error (`expected Comma, found Val`) is a source-level defect in the handoff
spec and drops the whole file, so that spec currently executes nothing at all;
that one is the most urgent, because a dropped file is the failure mode that looks
quietest.

Not diagnosed further here on purpose. These modules are the environment
policy/handoff surface Codex's lane owns end to end.

# `bin/simple` pointed at a 20-hour-stale ad-hoc scratch build, not the release binary

**Status:** FIXED (symlink restored 2026-08-05 07:05 UTC)
**Found:** 2026-08-05
**Severity:** MEDIUM — invalidated the binary-provenance assumption behind
every `bin/simple` invocation in this worktree for an unknown span of this
session, though its practical impact turned out to be limited (see below).
**Component:** `bin/simple` symlink

## What was found

`bin/simple` was a symlink to
`/tmp/claude-1000/.../scratchpad/simple-fixed`, an ad-hoc Rust seed debug
build (486MB, `Birth: 2026-08-04 10:34:25`) rather than the documented
canonical target `bin/release/x86_64-unknown-linux-gnu/simple` (per
`.claude/rules/structure.md`: "`bin/simple` → `release/<triple>/simple`
symlink"). The redirection was over 20 hours stale relative to when it was
discovered, and was never reverted after whatever earlier investigation
created it.

## Impact assessment

Every `bin/simple test`/`bin/simple run` invocation in this session ran
against the stale scratch build, not the canonical one, for however long the
redirection was in place. In practice this mattered less than the initial
discovery suggested, because:

- Both the stale scratch build and the canonical release binary are Rust
  **seed** builds (both print the bootstrap-seed warning) — there is no
  self-hosted binary deployed in this worktree at all, so results were
  already being attributed to "the seed" throughout, correctly.
- `.spl`-level test logic (coverage manifest gates, GPU session unit specs,
  selector-matching fixes) is read fresh from source on every invocation
  regardless of which Rust seed binary runs it, so staleness of the *Rust*
  build does not affect correctness of *Simple*-level logic tests. Re-running
  the coverage-manifest gate and GPU session specs after the fix reproduced
  identically to before the fix.
- It DOES matter for defects that live in the Rust runtime/compiler itself.
  One was caught directly by this: see
  `doc/08_tracking/bug/mlkem_ntt_simd_public_interface_probe_crashes_not_pass_2026-08-05.md`,
  where a claimed SIMD PASS was re-tested against both the stale and the
  corrected binary and crashed on both (different signal each time) — so in
  that specific case the symlink was not the cause of the discrepancy, but
  it had to be ruled out first, which is the point of this doc.

## Fix

```
ln -sfn release/x86_64-unknown-linux-gnu/simple bin/simple
```

`bin/release/x86_64-unknown-linux-gnu/simple` itself resolves (via a further
symlink hop) to the main checkout's shared `bin/release/` build output —
this is an intentional shared-build-artifact pattern across worktrees, not a
bug.

## Lesson

When re-verifying an agent's claim, check `readlink -f bin/simple` (or
whatever binary path a "binary under test" claim depends on) as part of the
contamination check, not just source-file md5s. A binary can drift out from
under a source tree that itself is stable.

## Reproduce

```
readlink -f bin/simple   # should resolve to .../bin/release/<triple>/simple
```

# Stage-2 native-build treats `--timeout 0` as immediate timeout

Status: open; blocks the source-matched Stage-3/4 admission needed by
`simple_build_test_abnormality_detection` verification.

## Evidence

- Compiler: `/mnt/data/worktrees/codex-01a01815/build/bootstrap/codex-unsafe-expr-stage2/stage2/x86_64-unknown-linux-gnu/simple`
- Source lane: `/mnt/data/worktrees/simple-work-20260824`
- Retained log: `build/native_probe/abnormality-stage3-retry2.log`
- Result: all 709 entry-closure files reported `timeout (0s)`.
- The invocation's `tee` pipeline masked the compiler's nonzero status; the
  next invocation must use `set -o pipefail`.

## Resume

Reuse `build/bootstrap/abnormality-stage3/x86_64-unknown-linux-gnu/native-cache`,
keep `SIMPLE_NO_STUB_FALLBACK=1`, omit `--timeout 0`, and run under
`set -o pipefail`. Do not delete the cache. This session exhausted the mandatory
three verify/fix cycles, so resume in a fresh scoped session.

## Owner and acceptance

Owner: bootstrap/native-build CLI maintainer. Decide and test whether zero means
unlimited or is rejected during argument validation. Acceptance requires one
source-matched Stage-3 artifact, its provenance/sanity receipt, then a Stage-4
artifact before normal test/docgen verification.

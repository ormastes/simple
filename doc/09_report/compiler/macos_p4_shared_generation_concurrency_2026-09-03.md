# macOS P4 Shared Generation Concurrency Audit

**Date:** 2026-09-03
**Scope:** concurrency row of `macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`

## Result

The shared generation store already had the required publication foundation:

- one cross-process authority lock;
- exclusive staging files and immutable generation names;
- bounded no-follow reads with digest verification;
- file and directory fsync before pointer visibility;
- generation-pinned readers;
- dead-owner lease recovery with PID start-identity protection;
- deterministic bounded GC that protects current and pinned generations.

The missing source behavior was identical-writer idempotence. A second writer
using the same expected parent, ordinal, and payload previously received
`parent-generation-changed` after the first writer published. Publication now
recognizes the exact current generation only after a no-follow bounded read and
byte comparison. It returns the immutable generation digest without rewriting
the generation or pointer. A differing payload still fails closed.

## Verification

- `shared_generation_publication_spec.spl`: **9/9 PASS** in interpreter mode.
- Added `identical-writer` to the mutation acceptance script; total mutation
  classes are now **5**: overflow, current protection, pin protection, GC pin
  protection, and identical-writer idempotence.
- Existing native fixtures remain the authority for conflicting thread writers,
  concurrent pinned readers/GC, and dead-process lease recovery.
- The acceptance fixture now derives its storage from
  `SIMPLE_WORKTREE_STORAGE_ROOT`; reusable/user storage remains separate.

## Unverified Native Slice

An attempted new all-process identical/conflicting writer fixture was removed
after the admitted compiler rejected it during discovery with `Unexpected token:
expected expression, found Indent`. The three-cycle cap was reached. No broken
fixture or native PASS claim is retained. A future admitted compiler run should
add process-level identical-writer contention evidence.

## Architecture Impact

No ABI or layout changed. Publication remains exclusive, immutable, no-follow,
bounded, and compatible with the two-root storage policy. The fast path adds
only one bounded generation read for an exact retry after the parent changed;
ordinary first publication and ordinary conflict behavior are unchanged.

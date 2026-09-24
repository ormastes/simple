# Pre-existing test-tree divergence stepped over by the robustness-pass spec landing

Range: `origin/main..a2a91b28d71a1a27fdb20ccaa7d02905ce01f5d1` — two new specs and one bug-record
closure from the 2026-09-18 robustness pass.

Recorded per the scoped-delta escape in `.claude/rules/vcs.md`, which requires
the pre-existing offender list to be written down before landing on a delta-PASS.
An unrecorded step-over is a violation even when the delta is clean.

Delta verdict (`scripts/check/check-test-tree-divergence-delta.shs origin/main HEAD`):

```
PASS — 3207 pre-existing offender(s), 0 introduced by this range
```

Base verdict at `origin/main`, for context. This is the red this landing steps
over, and it is not this change's debt:

```
FAIL — 3923 diverged vs 965 baselined (3067 new, 109 fixed-but-still-baselined);
32 mirror-only (31 unallowlisted, 0 stale-allowlist)
```

The range adds two files under `test/01_unit/` and edits one tracking record.
`test/01_unit/interpreter/` has no mirror under `test/unit/` at all;
`test/01_unit/lib/nogc_async_mut/` does, and the new
`cancellation_token_spec.spl` has no counterpart there — which is why the delta
check was run before pushing rather than after a failed push. It introduces zero
new divergence: the guard compares diverged PAIRS, and a file that exists on only
one side with no same-named sibling forms no pair.

Full offender list: `test_tree_divergence_preexisting_robustness_specs_2026-09-18.txt`
(3923 lines, sha256 `85aaf8d93678950e3094b9ceae4cb386da5ba1aeaf85140f5fa2cd76d26a8274`).

## Why this keeps recurring

This is at least the fifth such record (see
`test_tree_divergence_preexisting_stepover_2026-08-20.md`,
`preexisting_test_tree_divergence_stepped_over_gpu_landing_2026-08-25.md`,
`test_tree_divergence_preexisting_beta_release_2026-09-07.md`,
`review_admission_concurrency_2026-09-06_divergence_offenders.txt`,
`macos_stage4_deploy_2026-09-08_divergence_offenders.txt`). The base count has
moved 3944 -> 3923 diverged and 26 -> 32 mirror-only since 2026-09-07, so the
backlog is roughly flat while mirror-only grows. Each step-over is individually
correct and collectively the escape is doing the job it was designed to prevent:
keeping a long-standing red permanently steppable. Consolidating or retiring the
duplicate `test/unit` and `test/02_integration` mirror trees is the actual fix
and is not attempted here.

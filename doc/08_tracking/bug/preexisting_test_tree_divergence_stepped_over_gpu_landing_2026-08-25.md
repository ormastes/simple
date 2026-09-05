# Pre-existing test-tree divergence stepped over by the GPU hardening landing (2026-08-25)

**Status:** RECORD ONLY — not introduced here, not fixed here.

`sh scripts/check/check-test-tree-divergence.shs` is RED on `origin/main` independently of this
change: `FAIL — 876 diverged vs 854 baselined (27 new, 5 fixed-but-still-baselined); 1 mirror-only`.
Per `.claude/rules/vcs.md`, a landing that introduces **zero** new divergence may proceed on a
delta-PASS provided the pre-existing offender list is recorded. It is:

- Verdict: `check-test-tree-divergence-delta: PASS — 32 pre-existing offender(s), 0 introduced by this range`
  (range `737f86ad68b..db4da5266d0`, both sides read from COMMITTED content via `--ref`).
- Full list (876 diverged pairs, the 32 offender categories among them) saved alongside this
  record as the helper wrote it; head of the list:
  `integration:app/app_mcp_intensive_spec.spl`, `integration:app/check_log_modes_spec.spl`,
  `integration:app/cli_log_modes_spec.spl`, `integration:app/feature_gen_log_modes_spec.spl`,
  `integration:app/itf_log_modes_spec.spl`, `integration:app/linkers_log_modes_spec.spl`,
  `integration:app/llm_dashboard_log_modes_spec.spl`, …

New specs in this landing live only under `test/01_unit/` and are **not** copied into the
`test/unit/` mirror (`.claude/rules` forbids cp between mirror trees); the delta helper confirms
they add no offender.

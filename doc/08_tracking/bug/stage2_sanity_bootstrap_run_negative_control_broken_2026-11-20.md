# Stage 2 sanity FAIL: bootstrap CLI `run` dispatch broke the negative control (2026-11-20)

- **Status:** verification-pending
- **Severity:** P1 (blocks every Phase 2 bootstrap of release/1.0.0)
- **Introduced:** `3e932aabea0` (PR #10568, wave-h1-c, item #125)
- **First failing run:** release/1.0.0 `58f96ec6bd7` (last green: `60e1b1f5a34`)

## Symptom
`scripts/bootstrap/bootstrap-from-scratch.sh` Stage 2 sanity:
`error: sanity FAIL - 'run' negative control: rc 0, output '[build] phase=load_sources ...'`.
The "frontend smoke log is empty" line is a secondary diagnostic; frontend_status was 0.

## Root cause
#125 added a general `run` subcommand (`run_bootstrap_script`) to
`src/app/cli/bootstrap_main.spl`. The sanity gate (and ~8 other gates/tests:
`resume-stage3-from-admitted.sh`, `bootstrap-stage3/sanity.shs`,
`bootstrap-stage3-candidate-builder.shs`, `pure_simple_stage_sanity_spec.spl`, ...)
deliberately use `run <file>` as a NEGATIVE CONTROL that must exit 1 with
`unknown command 'run'` (the gate comment says "Do not fix it into a `run` that works").

## Repro (Stage 2 binary, `run src/compiler/bootstrap_admission/p2_add.spl`)
- 58f96ec6bd7 `simple.rejected`: rc=0, prints build progress then `5`.
- 60e1b1f5a34 `simple`: rc=1, `error: unknown command 'run'`.

## Fix
Revert the bootstrap_main.spl part of `3e932aabea0` (run dispatch, parser,
help line). Replace `bootstrap_main_run_dispatch_spec.spl` with
`test/01_unit/app/cli/bootstrap_main_run_rejected_spec.spl` pinning the contract
(measured: 1 of 3 examples fails before the fix, 3/3 pass after). Full-CLI `run` remains in `src/app/cli/main.spl`.

## Verification pending
Phase 2 bootstrap re-run passing Stage 2 sanity on the fixed tip.

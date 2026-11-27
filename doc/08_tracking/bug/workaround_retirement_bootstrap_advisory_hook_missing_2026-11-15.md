# Workaround retirement has no bootstrap advisory hook (2026-11-15)

Plan section 5 (`simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md`)
wants workaround retirement consulted at the next rebuild. No clean read-only
hook exists, so none was forced.

## Evidence
- `src/app/bootstrap_builder/workaround_rebuild.spl:108` (`workaround_rebuild_prepare_v1`)
  and `:180` (`workaround_rebuild_admit_v1`) have no caller anywhere under
  `src/` or `scripts/`; they require a full `WorkaroundRetirementV1` record
  (root-fix commit, exact hunks, admitted proofs) that nothing produces yet.
- `src/app/cli/bootstrap_check.spl:345` (`check_bootstrap_pipeline`) checks the
  compiler pipeline only; it holds no bug DB or workaround index.
- The sanctioned bootstrap is `scripts/bootstrap/bootstrap-from-scratch.sh`, which
  cannot call Simple report code before a compiler exists.

## Where it should go
After the Stage-N compiler is admitted in the bootstrap driver, call
`workaround_auto_retire_report_v1` (`src/app/bug/workaround_autoretire.spl`) for
every fixed/closed bug in `workaround_closure_bypass_findings_v1` and print the
lines to the log. Advisory only: it must not change bootstrap pass/fail.

## Unblock condition
A bootstrap driver entry in Simple (not the shell script) that runs after a
compiler is admitted and can load `doc/08_tracking/bug/bug_db.sdn`; plus a
producer for `WorkaroundRetirementV1` records so `workaround_rebuild_prepare_v1`
has a caller. Until then `simple check-dbs bugs` reports the same findings
(`closure_gate_bypass`, advisory).

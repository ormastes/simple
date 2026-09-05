# Current Stage 3 acceptance false closure

Status: fixed (2026-08-17)

Historical LIM-010 evidence and byte equality were previously sufficient for a
human tracking lane to call the current Stage 3 accepted, even though the
current transaction had no canonical Stage 3 provenance receipt and the Stage
4 gates had not completed. That made the tracking conclusion stronger than the
artifacts.

The bootstrap owner now starts with current acceptance explicitly unverified.
It promotes that state only after the Stage 4 essential-tools smoke, Stage 4
candidate-provenance verification, and a fresh replay of the Stage 3 sanity
receipt. It then writes a dedicated acceptance receipt binding the Stage 3
provenance, Stage 3 sanity, Stage 4 candidate, and Stage 4 provenance hashes.
The terminal bootstrap path fails closed unless this promotion occurred.

The exact regression test deletes Stage 4 provenance verification and proves
the acceptance contract rejects the modified producer. Adjacent sabotage cases
delete Stage 3 sanity re-verification and the essential-tools terminal-gate
field; both are rejected.

Evidence:

- `sh test/01_unit/scripts/bootstrap_stage3_current_acceptance_contract_test.shs`
  — PASS on 2026-08-17.

This closes only the false-closure defect. It deliberately does not claim that
a current-source Stage 3/4 bootstrap has completed; the separate Stage 3 RSS
termination record remains the authority for that execution blocker.
